import Breakdown.FracCert.GradientOrthogonalParts
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open scoped ContDiff ENNReal Convolution
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace GradientOrthogonalInternal

private abbrev mulFlip : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip

private theorem mulFlip_apply (a r : ℝ) : mulFlip a r = r * a := rfl

private theorem test_dir {φ : Space → ℝ} (hφ : IsTestScalar φ) (v : Space) :
    IsTestScalar (fun y => fderiv ℝ φ y v) :=
  ⟨(hφ.1.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const,
    hφ.2.fderiv_apply (𝕜 := ℝ) v⟩

private theorem second_dir {φ : Space → ℝ} (hφ : IsTestScalar φ) (y u v : Space) :
    fderiv ℝ (fun y => fderiv ℝ φ y u) y v = fderiv ℝ (fun y => fderiv ℝ φ y v) y u := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.1.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp) y
  rw [fderiv_clm_apply hdd (differentiableAt_const u), fderiv_clm_apply hdd (differentiableAt_const v)]
  simp only [ContinuousLinearMap.flip_apply, fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact (ContDiffAt.isSymmSndFDerivAt (hφ.1.contDiffAt (x := y)) (by simp; exact WithTop.coe_le_coe.2 le_top)) v u

theorem curl_symm {Q : Space → Space} (hQ : IsGradientField Q) (φ : Space → ℝ) (hφ : IsTestScalar φ)
    (j k : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector k) * inner ℝ (Q y) (unitVector j) =
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (Q y) (unitVector k) := by
  obtain ⟨q, -, -, -, hw⟩ := hQ
  have h1 := hw _ (test_dir hφ (unitVector k)) j
  have h2 := hw _ (test_dir hφ (unitVector j)) k
  have he : (fun y => fderiv ℝ (fun y => fderiv ℝ φ y (unitVector k)) y (unitVector j) * q y) =
      fun y => fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) y (unitVector k) * q y := by
    funext y
    rw [second_dir hφ]
  rw [he, h2] at h1
  exact (neg_inj.1 h1).symm

private theorem clm_zero_of_unit (D : Space →L[ℝ] ℝ) (h : ∀ j : Fin 3, D (unitVector j) = 0) : D = 0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro j
  simpa [unitVector] using h j

private theorem conv_hasFDerivAt_zero {C : Space → ℝ} (hc : Continuous C)
    (hd : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ k : Fin 3, ∫ y, fderiv ℝ φ y (unitVector k) * C y = 0)
    (ψ : Space → ℝ) (hψ : IsTestScalar ψ) (x : Space) :
    HasFDerivAt (C ⋆[mulFlip, volume] ψ) (0 : Space →L[ℝ] ℝ) x := by
  have hloc : LocallyIntegrable C volume := hc.locallyIntegrable
  have h1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have hD := hψ.2.hasFDerivAt_convolution_right mulFlip hloc h1 x
  suffices hz : (C ⋆[mulFlip.precompR Space, volume] fderiv ℝ ψ) x = 0 by
    rw [hz] at hD
    exact hD
  apply clm_zero_of_unit
  intro j
  rw [convolution_precompR_apply mulFlip hloc (hψ.2.fderiv ℝ) (h1.continuous_fderiv one_ne_zero) x
    (unitVector j), convolution_def]
  simp only [mulFlip_apply]
  have hχ : IsTestScalar (fun y => ψ (x - y)) :=
    ⟨hψ.1.comp (contDiff_const.sub contDiff_id), hψ.2.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hder : ∀ y, fderiv ℝ (fun y => ψ (x - y)) y (unitVector j) =
      -(fderiv ℝ ψ (x - y) (unitVector j)) := by
    intro y
    have hψd : DifferentiableAt ℝ ψ (x - y) := (h1.differentiable one_ne_zero).differentiableAt
    have : HasFDerivAt (fun y => ψ (x - y))
        ((fderiv ℝ ψ (x - y)).comp (0 - ContinuousLinearMap.id ℝ Space)) y :=
      hψd.hasFDerivAt.comp y ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [this.fderiv]
    simp
  have := hd _ hχ j
  simp only [hder, neg_mul, integral_neg, neg_eq_zero] at this
  exact this

private theorem bounded_of {C : Space → ℝ} (hc : Continuous C) (ht : Tendsto C (cocompact Space) (𝓝 0)) :
    ∃ M : ℝ, ∀ y, |C y| ≤ M := by
  have hev : ∀ᶠ y in cocompact Space, |C y| ≤ 1 := by
    have := ht.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with y hy
    simpa [Metric.mem_closedBall, Real.dist_eq] using hy
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 hev
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 1, fun y => ?_⟩
  by_cases hy : y ∈ K
  · exact (by simpa [Real.norm_eq_abs] using hB y hy : |C y| ≤ B).trans (le_max_left _ _)
  · exact (hKs hy).trans (le_max_right _ _)

private theorem conv_zero {C : Space → ℝ} (hc : Continuous C) (ht : Tendsto C (cocompact Space) (𝓝 0))
    (hd : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ k : Fin 3, ∫ y, fderiv ℝ φ y (unitVector k) * C y = 0)
    (ψ : Space → ℝ) (hψ : IsTestScalar ψ) : (C ⋆[mulFlip, volume] ψ) 0 = 0 := by
  obtain ⟨M, hM⟩ := bounded_of hc ht
  have hD := conv_hasFDerivAt_zero hc hd ψ hψ
  have hconst : ∀ x, (C ⋆[mulFlip, volume] ψ) x = (C ⋆[mulFlip, volume] ψ) 0 := fun x =>
    is_const_of_fderiv_eq_zero (fun z => (hD z).differentiableAt) (fun z => (hD z).fderiv) x 0
  have hform : ∀ x, (C ⋆[mulFlip, volume] ψ) x = ∫ s, ψ s * C (x - s) := by
    intro x
    rw [convolution_def]
    simp only [mulFlip_apply]
    rw [← integral_sub_left_eq_self _ volume x]
    simp only [sub_sub_cancel]
  have hlim : Tendsto (fun n : ℕ => ∫ s, ψ s * C ((n : ℝ) • unitVector 0 - s)) atTop (𝓝 0) := by
    have hψc : Continuous ψ := hψ.1.continuous
    have hint : Integrable (fun s => M * |ψ s|) volume :=
      ((hψc.integrable_of_hasCompactSupport hψ.2).abs).const_mul M
    have := tendsto_integral_of_dominated_convergence (fun s => M * |ψ s|)
      (F := fun (n : ℕ) s => ψ s * C ((n : ℝ) • unitVector 0 - s)) (f := fun _ => (0 : ℝ))
      (fun n => (hψc.mul (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      hint
      (fun n => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _))
      (Eventually.of_forall fun s => by
        have hcc : Tendsto (fun n : ℕ => (n : ℝ) • unitVector 0 - s) atTop (cocompact Space) := by
          apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : Space)
          have hn : ∀ n : ℕ, (n : ℝ) - ‖s‖ ≤ dist ((n : ℝ) • unitVector 0 - s) 0 := by
            intro n
            rw [dist_zero_right]
            have h1 : ‖(n : ℝ) • unitVector 0‖ = n := by simp [unitVector, norm_smul]
            have := norm_sub_norm_le ((n : ℝ) • unitVector 0) s
            linarith
          exact tendsto_atTop_mono hn (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        have := (ht.comp hcc).const_mul (ψ s)
        simpa using this)
    simpa using this
  have hseq : ∀ n : ℕ, (C ⋆[mulFlip, volume] ψ) 0 = ∫ s, ψ s * C ((n : ℝ) • unitVector 0 - s) := by
    intro n
    rw [← hform]
    exact (hconst _).symm
  exact tendsto_nhds_unique (tendsto_const_nhds.congr hseq) hlim

theorem zero_of_parts {C : Space → ℝ} (hc : Continuous C) (ht : Tendsto C (cocompact Space) (𝓝 0))
    (hd : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ k : Fin 3, ∫ y, fderiv ℝ φ y (unitVector k) * C y = 0) :
    C 0 = 0 := by
  let b : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity, by
      apply one_div_lt_one_div_of_lt (by positivity); linarith⟩
  have hr : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hr hc 0
  have hz : ∀ n, ((b n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] C) 0 = 0 := by
    intro n
    rw [← convolution_flip]
    exact conv_zero hc ht hd _ ⟨(b n).contDiff_normed, (b n).hasCompactSupport_normed⟩
  simp only [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end GradientOrthogonalInternal

open GradientOrthogonalInternal in
theorem gradientOrthogonal : GradientOrthogonalStatement := by
  intro Q ζ hQ hQ2 hζ
  have h := zero_of_parts (continuous_pairShift hζ.1 hQ2) (tendsto_pairShift hζ.1 hQ2)
    (integral_deriv_pairShift hζ hQ2 (curl_symm hQ))
  simpa [pairShift, real_inner_comm] using h

end SteadyCert

end Breakdown
