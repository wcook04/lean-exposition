import Breakdown.CertTorus.DecayStatements
import Breakdown.Uniqueness.FundSolMeanValue

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

namespace Internal

open Breakdown.FundSol

theorem init_three (a b c : Space) : Fin.init ![a, b, c] = ![a, b] := by
  ext i
  fin_cases i <;> rfl

theorem tail_three (a b c : Space) : Fin.tail ![a, b, c] = ![b, c] := by
  ext i
  fin_cases i <;> rfl

theorem iteratedFDeriv_two_fderiv_apply (g : Space → ℝ) (x a b c : Space) :
    iteratedFDeriv ℝ 2 (fderiv ℝ g) x ![a, b] c = iteratedFDeriv ℝ 3 g x ![a, b, c] := by
  rw [iteratedFDeriv_succ_apply_right (n := 2), init_three]
  rfl

theorem iteratedFDeriv_three_swap_head {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (x a b c : Space) :
    iteratedFDeriv ℝ 3 g x ![a, b, c] = iteratedFDeriv ℝ 3 g x ![b, a, c] := by
  rw [← iteratedFDeriv_two_fderiv_apply, ← iteratedFDeriv_two_fderiv_apply]
  have hs : IsSymmSndFDerivAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := ∞) le_rfl).contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)
  rw [IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hs)]

theorem iteratedFDeriv_three_swap_tail {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (x a b c : Space) :
    iteratedFDeriv ℝ 3 g x ![a, b, c] = iteratedFDeriv ℝ 3 g x ![a, c, b] := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 g) x :=
    hg.differentiable_iteratedFDeriv (by norm_cast) x
  rw [hd.iteratedFDeriv_succ_apply_left', hd.iteratedFDeriv_succ_apply_left', tail_three,
    tail_three]
  have hfun : (fun y => iteratedFDeriv ℝ 2 g y ![b, c]) =
      fun y => iteratedFDeriv ℝ 2 g y ![c, b] := by
    funext y
    have hs : IsSymmSndFDerivAt ℝ g y := hg.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)
    exact IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hs)
  rw [hfun]
  rfl

theorem scalarLaplacian_partial_eq_zero {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) {U : Set Space}
    (hU : IsOpen U) (hharm : ∀ x ∈ U, scalarSumSecondPartials g x = 0) (i : Fin 3) {x : Space}
    (hx : x ∈ U) : scalarSumSecondPartials (fun z => fderiv ℝ g z (unitVector i)) x = 0 := by
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (m := ∞) le_rfl
  have hD2 : Differentiable ℝ (iteratedFDeriv ℝ 2 g) :=
    hg.differentiable_iteratedFDeriv (by norm_cast)
  have hterm : ∀ j, secondPartial (fun z => fderiv ℝ g z (unitVector i)) j j x =
      iteratedFDeriv ℝ 3 g x ![unitVector i, unitVector j, unitVector j] := by
    intro j
    have hcomp : (fun z => fderiv ℝ g z (unitVector i)) =
        (ContinuousLinearMap.apply ℝ ℝ (unitVector i)) ∘ fderiv ℝ g := rfl
    rw [secondPartial, hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hD1.contDiffAt
      (by norm_cast)]
    rw [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.apply_apply, iteratedFDeriv_two_fderiv_apply,
      iteratedFDeriv_three_swap_tail hg, iteratedFDeriv_three_swap_head hg]
  have hd : ∀ j, DifferentiableAt ℝ (fun y => secondPartial g j j y) x := fun j =>
    (hD2 x).continuousMultilinear_apply_const _
  have happly : ∀ j, fderiv ℝ (fun y => secondPartial g j j y) x (unitVector i) =
      iteratedFDeriv ℝ 3 g x ![unitVector i, unitVector j, unitVector j] := by
    intro j
    rw [(hD2 x).iteratedFDeriv_succ_apply_left', tail_three]
    rfl
  have hev : scalarSumSecondPartials g =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) hharm
  have hzero : fderiv ℝ (scalarSumSecondPartials g) x = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply 0
  have hsum : fderiv ℝ (scalarSumSecondPartials g) x =
      ∑ j, fderiv ℝ (fun y => secondPartial g j j y) x := by
    have e : scalarSumSecondPartials g = fun y => ∑ j, secondPartial g j j y := rfl
    rw [e, fderiv_fun_sum (fun j _ => hd j)]
  calc scalarSumSecondPartials (fun z => fderiv ℝ g z (unitVector i)) x
      = ∑ j, iteratedFDeriv ℝ 3 g x ![unitVector i, unitVector j, unitVector j] := by
        unfold scalarSumSecondPartials
        exact Finset.sum_congr rfl fun j _ => hterm j
    _ = fderiv ℝ (scalarSumSecondPartials g) x (unitVector i) := by
        rw [hsum, _root_.sum_apply]
        exact Finset.sum_congr rfl fun j _ => (happly j).symm
    _ = 0 := by rw [hzero]; rfl

theorem integrableOn_ball_of_continuous {f : Space → ℝ} (hf : Continuous f) (y : Space)
    (r : ℝ) : IntegrableOn f (ball y r) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall y r)).mono_set ball_subset_closedBall

theorem memLp_two_restrict_ball {f : Space → ℝ} (hf : Continuous f) (y : Space) (r : ℝ) :
    MemLp f (ENNReal.ofReal 2) (volume.restrict (ball y r)) := by
  rw [show ENNReal.ofReal 2 = 2 by norm_num]
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
    (integrableOn_ball_of_continuous (hf.pow 2) y r)

theorem abs_le_of_meanValue (hMV : HarmonicMeanValue) {K : ℝ}
    (hK : ∀ ρ, 0 < ρ → ∀ x, mollifier ρ x ≤ K * ρ⁻¹ ^ 3) {h : Space → ℝ}
    (hh : ContDiff ℝ ∞ h) {y : Space} {r : ℝ} (hr : 0 < r)
    (hharm : ∀ x ∈ ball y r, scalarSumSecondPartials h x = 0) :
    |h y| ≤ (K * (r / 2)⁻¹ ^ 3) ^ (1 / 2 : ℝ) * (∫ x in ball y (r / 2), h x ^ 2) ^ (1 / 2 : ℝ) := by
  have hρ : 0 < r / 2 := by positivity
  have hmv := hMV h y r hr hh hharm (r / 2) hρ (by linarith)
  have hmc : Continuous (fun z : Space => mollifier (r / 2) (y - z)) :=
    (contDiff_mollifier (r / 2)).continuous.comp (continuous_const.sub continuous_id)
  have hout : ∀ z, z ∉ ball y (r / 2) → mollifier (r / 2) (y - z) = 0 := by
    intro z hz
    apply mollifier_eq_zero hρ
    rw [mem_ball, dist_eq_norm, not_lt] at hz
    rwa [norm_sub_rev]
  have hnn : ∀ z, 0 ≤ mollifier (r / 2) (y - z) := fun z => mollifier_nonneg hρ _
  have h1 : |h y| ≤ ∫ z in ball y (r / 2), mollifier (r / 2) (y - z) * |h z| := by
    rw [hmv]
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hout z hz, zero_mul])]
    congr 1
    funext z
    rw [abs_mul, abs_of_nonneg (hnn z)]
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (ball y (r / 2)))
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall fun z => hnn z)
    (Filter.Eventually.of_forall fun z => abs_nonneg (h z))
    (memLp_two_restrict_ball hmc y (r / 2))
    (memLp_two_restrict_ball hh.continuous.abs y (r / 2))
  have hA : ∫ z in ball y (r / 2), mollifier (r / 2) (y - z) ^ (2 : ℝ) ≤ K * (r / 2)⁻¹ ^ 3 := by
    calc ∫ z in ball y (r / 2), mollifier (r / 2) (y - z) ^ (2 : ℝ)
        ≤ ∫ z in ball y (r / 2), K * (r / 2)⁻¹ ^ 3 * mollifier (r / 2) (y - z) := by
          refine integral_mono ?_ ?_ fun z => ?_
          · simp_rw [Real.rpow_two]
            exact integrableOn_ball_of_continuous (hmc.pow 2) y _
          · exact integrableOn_ball_of_continuous (continuous_const.mul hmc) y _
          · rw [Real.rpow_two, sq]
            exact mul_le_mul_of_nonneg_right (hK _ hρ _) (hnn z)
      _ = K * (r / 2)⁻¹ ^ 3 := by
          rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero hout,
            integral_sub_left_eq_self (fun z => mollifier (r / 2) z) volume y,
            integral_mollifier hρ, mul_one]
  have hB : ∫ z in ball y (r / 2), |h z| ^ (2 : ℝ) = ∫ z in ball y (r / 2), h z ^ 2 := by
    congr 1
    funext z
    rw [Real.rpow_two, sq_abs]
  have hA0 : 0 ≤ ∫ z in ball y (r / 2), mollifier (r / 2) (y - z) ^ (2 : ℝ) :=
    integral_nonneg fun z => Real.rpow_nonneg (hnn z) _
  have hB0 : 0 ≤ (∫ z in ball y (r / 2), h z ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun z => sq_nonneg _) _
  rw [hB] at h2
  calc |h y| ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := by
        norm_num only at hA ⊢
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hA0 hA (by norm_num)) hB0

theorem opNorm_le_sum_abs (L : Space →L[ℝ] ℝ) : ‖L‖ ≤ ∑ i, |L (unitVector i)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
    fun v => ?_
  have hv : v = ∑ i, v i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, unitVector]
  calc ‖L v‖ = |∑ i, v i * L (unitVector i)| := by
        rw [Real.norm_eq_abs]
        conv_lhs => rw [hv]
        simp only [map_sum, map_smul, smul_eq_mul]
    _ ≤ ∑ i, |v i * L (unitVector i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖v‖ * |L (unitVector i)| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using PiLp.norm_apply_le v i) (abs_nonneg _)
    _ = (∑ i, |L (unitVector i)|) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

end Internal

open Internal Breakdown.FundSol

theorem harmonicGradientBound_of_meanValue : HarmonicMeanValue → HarmonicGradientBound := by
  intro hMV
  obtain ⟨Cm, hCm⟩ := mollifier_le
  have hC0 : 0 ≤ max Cm 0 := le_max_right _ _
  refine ⟨3 * ((8 * max Cm 0) ^ (1 / 2 : ℝ)), fun g y r hr hg hharm => ?_⟩
  have hK : ∀ ρ, 0 < ρ → ∀ x, mollifier ρ x ≤ max Cm 0 * ρ⁻¹ ^ 3 := fun ρ hρ x =>
    (hCm ρ hρ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hcd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hT0 : 0 ≤ (∫ x in ball y r, ‖fderiv ℝ g x‖ ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun x => sq_nonneg _) _
  have hcomp : ∀ i, |fderiv ℝ g y (unitVector i)| ≤ (8 * max Cm 0) ^ (1 / 2 : ℝ) *
      r ^ (-(3 / 2 : ℝ)) * (∫ x in ball y r, ‖fderiv ℝ g x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    intro i
    have hci : Continuous (fun z => fderiv ℝ g z (unitVector i)) :=
      hcd.clm_apply continuous_const
    have hh : ContDiff ℝ ∞ (fun z => fderiv ℝ g z (unitVector i)) :=
      (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hb := abs_le_of_meanValue hMV hK hh hr
      (fun x hx => scalarLaplacian_partial_eq_zero hg isOpen_ball hharm i hx)
    refine hb.trans ?_
    have hKr : (max Cm 0 * (r / 2)⁻¹ ^ 3) ^ (1 / 2 : ℝ) =
        (8 * max Cm 0) ^ (1 / 2 : ℝ) * r ^ (-(3 / 2 : ℝ)) := by
      have e1 : max Cm 0 * (r / 2)⁻¹ ^ 3 = (8 * max Cm 0) * r ^ (-(3 : ℝ)) := by
        rw [Real.rpow_neg hr.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hr0 : r ≠ 0 := hr.ne'
        field_simp
        ring
      rw [e1, Real.mul_rpow (mul_nonneg (by norm_num) hC0) (Real.rpow_nonneg hr.le _),
        ← Real.rpow_mul hr.le]
      norm_num
    have hS : (∫ x in ball y (r / 2), fderiv ℝ g x (unitVector i) ^ 2) ≤
        ∫ x in ball y r, ‖fderiv ℝ g x‖ ^ 2 := by
      calc (∫ x in ball y (r / 2), fderiv ℝ g x (unitVector i) ^ 2)
          ≤ ∫ x in ball y (r / 2), ‖fderiv ℝ g x‖ ^ 2 := by
            refine integral_mono (integrableOn_ball_of_continuous (hci.pow 2) y _)
              (integrableOn_ball_of_continuous (hcd.norm.pow 2) y _) fun x => ?_
            have hle : |fderiv ℝ g x (unitVector i)| ≤ ‖fderiv ℝ g x‖ := by
              have := (fderiv ℝ g x).le_opNorm (unitVector i)
              rwa [Real.norm_eq_abs, show ‖unitVector i‖ = 1 by simp [unitVector], mul_one]
                at this
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hle 2
        _ ≤ ∫ x in ball y r, ‖fderiv ℝ g x‖ ^ 2 :=
            setIntegral_mono_set (integrableOn_ball_of_continuous (hcd.norm.pow 2) y _)
              (Filter.Eventually.of_forall fun x => sq_nonneg _)
              (ball_subset_ball (by linarith)).eventuallyLE
    rw [hKr]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (integral_nonneg fun x => sq_nonneg _) hS (by norm_num))
      (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hC0) _) (Real.rpow_nonneg hr.le _))
  calc ‖fderiv ℝ g y‖ ≤ ∑ i, |fderiv ℝ g y (unitVector i)| := opNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin 3, (8 * max Cm 0) ^ (1 / 2 : ℝ) * r ^ (-(3 / 2 : ℝ)) *
        (∫ x in ball y r, ‖fderiv ℝ g x‖ ^ 2) ^ (1 / 2 : ℝ) :=
          Finset.sum_le_sum fun i _ => hcomp i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Breakdown.FarField
