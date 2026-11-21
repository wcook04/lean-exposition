import Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal


theorem curl_field_div (u : Space → Space) (hu : ContDiff ℝ 3 u) (y : Space) :
    divergenceAt (fun x => curlVec (fderiv ℝ u x)) y = 0 := by
  have h2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hdω : DifferentiableAt ℝ (fun x => curlVec (fderiv ℝ u x)) y :=
    ((curlCLM.contDiff.comp (hu.fderiv_right (m := 2) (by norm_num))).differentiable (by norm_num)) y
  have e : ∀ i : Fin 3, fderiv ℝ (fun x => curlVec (fderiv ℝ u x)) y (unitVector i) i =
      ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol i a b *
        fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector i) (unitVector a) b := fun i => by
    rw [← fderiv_component _ hdω, curl_deriv u h2]
  simp only [divergenceAt, e]
  have s10 := d2_symm_two u h2 y (unitVector 1) (unitVector 0)
  have s20 := d2_symm_two u h2 y (unitVector 2) (unitVector 0)
  have s21 := d2_symm_two u h2 y (unitVector 2) (unitVector 1)
  simp only [Fin.sum_univ_three, eps_000, eps_001, eps_002, eps_010, eps_011, eps_012, eps_020, eps_021,
    eps_022, eps_100, eps_101, eps_102, eps_110, eps_111, eps_112, eps_120, eps_121, eps_122, eps_200,
    eps_201, eps_202, eps_210, eps_211, eps_212, eps_220, eps_221, eps_222]
  simp only [s10, s20, s21]
  ring

theorem sumSecondPartials_slice (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (σ : ℝ)
    (hs : SliceBounds P v σ) :
    ∫ y, inner ℝ (-secondDerivTrace (secondDerivField v σ y)) (-secondDerivTrace (secondDerivField v σ y)) =
      ∫ y, matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) := by
  have hsm : ContDiff ℝ ∞ (v σ) := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hu3 : ContDiff ℝ 3 (v σ) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContDiff ℝ 2 (v σ) := hu3.of_le (by norm_num)
  have hd : ∀ y, divergenceAt (v σ) y = 0 := hv.divergence_free σ
  have hω : ContDiff ℝ 2 (fun x => curlVec (fderiv ℝ (v σ) x)) :=
    curlCLM.contDiff.comp (hu3.fderiv_right (m := 2) (by norm_num))
  have hdω : Differentiable ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) := hω.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fun x => fderiv ℝ (v σ) x) :=
    (hu2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have pt : ∀ y, inner ℝ (-secondDerivTrace (secondDerivField v σ y)) (-secondDerivTrace (secondDerivField v σ y)) =
      ‖curlVec (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)‖ ^ 2 := by
    intro y
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : (-secondDerivTrace (secondDerivField v σ y)) i =
        curlVec (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) i := by
      rw [secondDerivField, ssp_curl (v σ) hu2 hd y i, curlVec_apply]
      simp only [fderiv_component _ (hdω y)]
    rw [hc]
  simp_rw [pt]
  have eω : ∀ y, fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y =
      curlCLM.comp (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y) := fun y => fderiv_clm_left curlCLM (hdd y)
  have h1 : Integrable (fun y => ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y‖ ^ 2) := by
    refine (hs.second.const_mul (‖curlCLM‖ ^ 2)).mono'
      ((hω.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), eω, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le _ _) 2
  have h0 : Integrable (fun y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
    refine (hs.first.const_mul (‖curlCLM‖ ^ 2)).mono'
      ((hω.continuous.norm.pow 2).div ((continuous_const.add continuous_norm).pow 2)
        (fun y => (by positivity : (0 : ℝ) < (1 + ‖y‖) ^ 2).ne')).aestronglyMeasurable
      (Eventually.of_forall (fun y => ?_))
    have hp : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg y])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (div_le_self (sq_nonneg _) hp).trans ?_
    rw [← curlCLM_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (curlCLM.le_opNorm _) 2
  exact curl_energy _ hω (curl_field_div (v σ) hu3) h1 h0

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
