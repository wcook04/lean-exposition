import Breakdown.Weak.StatementsSlice
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff Convolution

noncomputable section

namespace Breakdown.WeakProfile

private abbrev smulFlip : Space →L[ℝ] ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip

private theorem smulFlip_apply (a : Space) (r : ℝ) : smulFlip a r = r • a := rfl

private theorem clm_eq_zero_of_unitVector (D : Space →L[ℝ] Space)
    (h : ∀ j : Fin 3, D (unitVector j) = 0) : D = 0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro j
  simpa [unitVector] using h j

private theorem conv_fderiv_eq_zero (f : Space → Space) (hloc : LocallyIntegrable f volume)
    (hzero : ∀ φ : Space → ℝ, IsTestFunction φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = 0)
    (ψ : Space → ℝ) (hψ : IsTestFunction ψ) (x : Space) :
    HasFDerivAt (f ⋆[smulFlip, volume] ψ) (0 : Space →L[ℝ] Space) x := by
  have h1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have hd := hψ.2.hasFDerivAt_convolution_right smulFlip hloc h1 x
  suffices hz : (f ⋆[smulFlip.precompR Space, volume] fderiv ℝ ψ) x = 0 by
    rw [hz] at hd
    exact hd
  apply clm_eq_zero_of_unitVector
  intro j
  rw [convolution_precompR_apply smulFlip hloc (hψ.2.fderiv ℝ) (h1.continuous_fderiv one_ne_zero) x
    (unitVector j), convolution_def]
  simp only [smulFlip_apply]
  have hχ : IsTestFunction (fun y => ψ (x - y)) := by
    refine ⟨hψ.1.comp (contDiff_const.sub contDiff_id), ?_⟩
    exact hψ.2.comp_homeomorph (Homeomorph.subLeft x)
  have hder : ∀ y, fderiv ℝ (fun y => ψ (x - y)) y (unitVector j) =
      -(fderiv ℝ ψ (x - y) (unitVector j)) := by
    intro y
    have hψd : DifferentiableAt ℝ ψ (x - y) :=
      (h1.differentiable one_ne_zero).differentiableAt
    have : HasFDerivAt (fun y => ψ (x - y))
        ((fderiv ℝ ψ (x - y)).comp (0 - ContinuousLinearMap.id ℝ Space)) y :=
      hψd.hasFDerivAt.comp y ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [this.fderiv]
    simp
  have := hzero _ hχ j
  simp only [hder, neg_smul, integral_neg, neg_eq_zero] at this
  exact this

private theorem conv_const (f : Space → Space) (hloc : LocallyIntegrable f volume)
    (hzero : ∀ φ : Space → ℝ, IsTestFunction φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = 0)
    (ψ : Space → ℝ) (hψ : IsTestFunction ψ) (x y : Space) :
    (f ⋆[smulFlip, volume] ψ) x = (f ⋆[smulFlip, volume] ψ) y := by
  have hD := conv_fderiv_eq_zero f hloc hzero ψ hψ
  exact is_const_of_fderiv_eq_zero (fun z => (hD z).differentiableAt) (fun z => (hD z).fderiv) x y

private theorem conv_enorm_le (f : Space → Space) (hfm : AEStronglyMeasurable f volume)
    (ψ : Space → ℝ) (hψc : Continuous ψ) (R : ℝ) (hR : ∀ z : Space, R < ‖z‖ → ψ z = 0)
    (v : Space) :
    ‖(f ⋆[smulFlip, volume] ψ) v‖ₑ ≤
      (∫⁻ t, ‖ψ t‖ₑ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)) *
        (∫⁻ t, (Metric.closedBall v R).indicator (fun t => ‖f t‖ₑ) t ^ (6 : ℝ)) ^ (1 / (6 : ℝ)) := by
  rw [convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ t, ‖smulFlip (f t) (ψ (v - t))‖ₑ =
      ((fun t => ‖ψ (v - t)‖ₑ) * (Metric.closedBall v R).indicator (fun t => ‖f t‖ₑ)) t := by
    intro t
    rw [smulFlip_apply, enorm_smul, Pi.mul_apply]
    by_cases ht : t ∈ Metric.closedBall v R
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      have hlt : R < ‖v - t‖ := by
        rw [Metric.mem_closedBall, not_le, dist_eq_norm] at ht
        rwa [norm_sub_rev]
      simp [hR _ hlt]
  simp_rw [hpt]
  have hpq : (6 / 5 : ℝ).HolderConjugate 6 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hA : AEMeasurable (fun t => ‖ψ (v - t)‖ₑ) volume :=
    (hψc.comp (continuous_const.sub continuous_id)).enorm.aemeasurable
  have hB : AEMeasurable ((Metric.closedBall v R).indicator (fun t => ‖f t‖ₑ)) volume :=
    hfm.enorm.indicator Metric.isClosed_closedBall.measurableSet
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hA hB).trans_eq ?_
  congr 2
  exact lintegral_sub_left_eq_self (fun z => ‖ψ z‖ₑ ^ (6 / 5 : ℝ)) v

private theorem ball_lintegral_tendsto (f : Space → Space) (hf : MemLp f 6 volume) (R : ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ t, (Metric.closedBall ((n : ℝ) • unitVector 0) R).indicator
      (fun t => ‖f t‖ₑ) t ^ (6 : ℝ)) atTop (𝓝 0) := by
  have hfin : ∫⁻ t, ‖f t‖ₑ ^ (6 : ℝ) < (⊤ : ℝ≥0∞) := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num)
      hf.eLpNorm_lt_top
    simpa using this
  have hlim := tendsto_lintegral_of_dominated_convergence' (μ := volume)
    (F := fun n : ℕ => fun t => (Metric.closedBall ((n : ℝ) • unitVector 0) R).indicator
      (fun t => ‖f t‖ₑ) t ^ (6 : ℝ)) (f := fun _ => 0) (fun t => ‖f t‖ₑ ^ (6 : ℝ))
    (fun n => ((hf.1.enorm.indicator Metric.isClosed_closedBall.measurableSet).pow_const _))
    (fun n => Eventually.of_forall fun t => by
      by_cases ht : t ∈ Metric.closedBall ((n : ℝ) • unitVector 0) R
      · simp only [Set.indicator_of_mem ht, le_refl]
      · simp only [Set.indicator_of_notMem ht]
        rw [ENNReal.zero_rpow_of_pos (by norm_num)]
        exact zero_le)
    hfin.ne
    (Eventually.of_forall fun t => by
      obtain ⟨N, hN⟩ := exists_nat_gt (‖t‖ + R)
      apply tendsto_const_nhds.congr'
      rw [EventuallyEq, eventually_atTop]
      refine ⟨N, fun n hn => ?_⟩
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hout : t ∉ Metric.closedBall ((n : ℝ) • unitVector 0) R := by
        rw [Metric.mem_closedBall, not_le, dist_eq_norm]
        have hnorm : ‖(n : ℝ) • unitVector 0‖ = n := by
          simp [unitVector, norm_smul]
        have := norm_sub_norm_le ((n : ℝ) • unitVector 0) t
        rw [norm_sub_rev] at this
        linarith
      simp only [Set.indicator_of_notMem hout]
      rw [ENNReal.zero_rpow_of_pos (by norm_num)])
  simpa using hlim

private theorem conv_eq_zero (f : Space → Space) (hf : MemLp f 6 volume)
    (hzero : ∀ φ : Space → ℝ, IsTestFunction φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = 0)
    (ψ : Space → ℝ) (hψ : IsTestFunction ψ) :
    (f ⋆[smulFlip, volume] ψ) 0 = 0 := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  obtain ⟨R, hRs⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : Space)
  have hR : ∀ z : Space, R < ‖z‖ → ψ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hRs hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hψc : Continuous ψ := hψ.1.continuous
  set K := (∫⁻ t, ‖ψ t‖ₑ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)) with hK
  have hKfin : K ≠ (⊤ : ℝ≥0∞) := by
    have hm : MemLp ψ (ENNReal.ofReal (6 / 5)) volume := hψc.memLp_of_hasCompactSupport hψ.2
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by simp)
      hm.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal (by norm_num)] at this
    exact (ENNReal.rpow_lt_top_of_nonneg (y := 1 / (6 / 5 : ℝ)) (by norm_num) this.ne).ne
  have hT := ball_lintegral_tendsto f hf R
  have hT2 : Tendsto (fun n : ℕ => K * (∫⁻ t, (Metric.closedBall ((n : ℝ) • unitVector 0) R).indicator
      (fun t => ‖f t‖ₑ) t ^ (6 : ℝ)) ^ (1 / (6 : ℝ))) atTop (𝓝 0) := by
    have h0 := ((ENNReal.continuous_rpow_const (y := 1 / (6 : ℝ))).tendsto 0).comp hT
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h0
    have := ENNReal.Tendsto.const_mul h0 (Or.inr hKfin)
    simpa using this
  have hle : ‖(f ⋆[smulFlip, volume] ψ) 0‖ₑ ≤ 0 := by
    refine ge_of_tendsto' hT2 fun n => ?_
    rw [conv_const f hloc hzero ψ hψ 0 ((n : ℝ) • unitVector 0)]
    exact conv_enorm_le f hf.1 ψ hψc R hR _
  exact enorm_eq_zero.mp (le_antisymm hle (zero_le))

theorem zeroGradientSix_holds : ZeroGradientSix := by
  intro f hf hzero
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have h := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg hgc => by
    have hψ : IsTestFunction (fun z => g (-z)) :=
      ⟨hg.comp contDiff_neg, hgc.comp_homeomorph (Homeomorph.neg Space)⟩
    have := conv_eq_zero f hf hzero _ hψ
    rw [convolution_def] at this
    simpa [smulFlip_apply] using this)
  filter_upwards [h] with x hx
  simpa using hx

end Breakdown.WeakProfile
