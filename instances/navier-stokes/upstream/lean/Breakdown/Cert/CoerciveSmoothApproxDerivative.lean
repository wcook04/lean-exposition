import Breakdown.Cert.CoerciveSmoothApproxKernel

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem convolution_fderiv_apply (n : ℕ) {f : ℝ × Space → Space} (hf : LocallyIntegrable f volume)
    (x w : ℝ × Space) :
    fderiv ℝ (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x w =
      ((fun t => fderiv ℝ (kernel n) t w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  have := volume_prod_invariantClass
  have hd := (kernel_hasCompactSupport n).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((kernel_contDiff n).of_le (by exact_mod_cast le_top)) hf x
  have hex := ((kernel_hasCompactSupport n).fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ℝ × Space))
    ((kernel_contDiff n).continuous_fderiv (by simp)) hf x
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
  simp

theorem mollify_fderiv_eq (n : ℕ) {v : ℝ → Space → Space} (hv : LocallyIntegrable (joint v) volume)
    (σ : ℝ) (y e : Space) :
    fderiv ℝ (mollify n v σ) y e =
      ((fun t => fderiv ℝ (kernel n) t (0, e)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint v)
        (σ, y) := by
  have hdiff : DifferentiableAt ℝ (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint v) (σ, y) :=
    (mollify_smooth n hv).differentiable (by simp) (σ, y)
  have h1 : HasFDerivAt (mollify n v σ)
      ((fderiv ℝ (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint v) (σ, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)
  rw [h1.fderiv]
  simp [convolution_fderiv_apply n hv]

theorem joint_apply_locallyIntegrable {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : LocallyIntegrable (joint G) volume) (e : Space) :
    LocallyIntegrable (joint (fun s x => G s x e)) volume :=
  (hG.smul ‖e‖).mono ((ContinuousLinearMap.apply ℝ Space e).continuous.comp_aestronglyMeasurable
    hG.aestronglyMeasurable) (Eventually.of_forall fun z => by
      rw [Pi.smul_apply, norm_smul, norm_norm]
      simpa [joint, mul_comm] using (G z.1 z.2).le_opNorm e)

theorem kernel_shift_testFunction (n : ℕ) (σ s : ℝ) (y : Space) :
    IsTestFunction (fun z : Space => kernel n ((σ, y) - (s, z))) := by
  refine ⟨(kernel_contDiff n).comp (contDiff_const.sub (contDiff_const.prodMk contDiff_id)), ?_⟩
  have hb : HasCompactSupport (fun z : Space => (spaceBump n).normed volume (y - z)) :=
    ((spaceBump n).hasCompactSupport_normed (μ := volume)).comp_homeomorph (Homeomorph.subLeft y)
  have heq : (fun z : Space => kernel n ((σ, y) - (s, z))) =
      (fun _ : Space => (timeBump n).normed volume (σ - s)) *
        (fun z : Space => (spaceBump n).normed volume (y - z)) := by
    funext z
    simp [kernel]
  rw [heq]
  exact hb.mul_left

theorem kernel_shift_fderiv (n : ℕ) (σ s : ℝ) (y z e : Space) :
    fderiv ℝ (fun z : Space => kernel n ((σ, y) - (s, z))) z e =
      -fderiv ℝ (kernel n) ((σ, y) - (s, z)) (0, e) := by
  have hk : DifferentiableAt ℝ (kernel n) ((σ, y) - (s, z)) :=
    (kernel_contDiff n).differentiable (by simp) _
  have h1 : HasFDerivAt (fun z : Space => kernel n ((σ, y) - (s, z)))
      ((fderiv ℝ (kernel n) ((σ, y) - (s, z))).comp (-(ContinuousLinearMap.inr ℝ ℝ Space))) z := by
    have hin : HasFDerivAt (fun z : Space => (σ, y) - (s, z))
        (-(ContinuousLinearMap.inr ℝ ℝ Space)) z := by
      have := ((hasFDerivAt_prodMk_right (𝕜 := ℝ) s z).const_sub (σ, y))
      simpa using this
    exact hk.hasFDerivAt.comp z hin
  rw [h1.fderiv]
  simp

theorem kernel_partial_eq (n : ℕ) {v Gc : ℝ → Space → Space}
    (hv : LocallyIntegrable (joint v) volume) (hG : LocallyIntegrable (joint Gc) volume) (i : Fin 3)
    (hw : ∀ᵐ s, ∀ φ, IsTestFunction φ →
      ∫ z, φ z • Gc s z = -∫ z, fderiv ℝ φ z (unitVector i) • v s z) (σ : ℝ) (y : Space) :
    ((fun t => fderiv ℝ (kernel n) t (0, unitVector i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      joint v) (σ, y) = mollify n Gc σ y := by
  have := volume_prod_invariantClass
  set x : ℝ × Space := (σ, y)
  have hc1 : Continuous (fun t => fderiv ℝ (kernel n) (x - t) (0, unitVector i)) :=
    (((kernel_contDiff n).continuous_fderiv (by simp)).clm_apply continuous_const).comp
      (continuous_const.sub continuous_id)
  have hs1 : HasCompactSupport (fun t => fderiv ℝ (kernel n) (x - t) (0, unitVector i)) :=
    ((kernel_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (0, unitVector i)).comp_homeomorph
      (Homeomorph.subLeft x)
  have hc2 : Continuous (fun t => kernel n (x - t)) :=
    (kernel_contDiff n).continuous.comp (continuous_const.sub continuous_id)
  have hs2 : HasCompactSupport (fun t => kernel n (x - t)) :=
    (kernel_hasCompactSupport n).comp_homeomorph (Homeomorph.subLeft x)
  have i1 := hv.integrable_smul_left_of_hasCompactSupport hc1 hs1
  have i2 := hG.integrable_smul_left_of_hasCompactSupport hc2 hs2
  unfold mollify
  rw [convolution_eq_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [Measure.volume_eq_prod] at i1 i2 ⊢
  rw [integral_prod _ i1, integral_prod _ i2]
  refine integral_congr_ae ?_
  filter_upwards [hw] with s hs
  have e := hs _ (kernel_shift_testFunction n σ s y)
  simp only [kernel_shift_fderiv, neg_smul, integral_neg, neg_neg] at e
  simpa [joint, x] using e.symm

theorem mollify_partial (n : ℕ) {f : ℝ → Space → Space} {F : ℝ → Space → (Space →L[ℝ] Space)}
    (hf : LocallyIntegrable (joint f) volume) (hF : LocallyIntegrable (joint F) volume)
    (hw : ∀ᵐ s, IsWeakGradient (f s) (F s)) (i : Fin 3) (σ : ℝ) (y : Space) :
    fderiv ℝ (mollify n f σ) y (unitVector i) = mollify n (fun s x => F s x (unitVector i)) σ y := by
  rw [mollify_fderiv_eq n hf]
  exact kernel_partial_eq n hf (joint_apply_locallyIntegrable hF _) i
    (hw.mono fun s hs φ hφ => hs.2.2 φ hφ i) σ y

theorem kernel_smul_integrable (n : ℕ) {w : ℝ → Space → Space}
    (hw : LocallyIntegrable (joint w) volume) (x : ℝ × Space) :
    Integrable (fun t => kernel n (x - t) • joint w t) volume := by
  have := volume_prod_invariantClass
  exact hw.integrable_smul_left_of_hasCompactSupport
    ((kernel_contDiff n).continuous.comp (continuous_const.sub continuous_id))
    ((kernel_hasCompactSupport n).comp_homeomorph (Homeomorph.subLeft x))

theorem mollify_eq_integral (n : ℕ) (w : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    mollify n w σ y = ∫ t, kernel n ((σ, y) - t) • joint w t := by
  have := volume_prod_invariantClass
  unfold mollify
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply]

theorem mollify_component (n : ℕ) {w : ℝ → Space → Space} (hw : LocallyIntegrable (joint w) volume)
    (σ : ℝ) (y : Space) (i : Fin 3) :
    mollify n w σ y i = ∫ t, kernel n ((σ, y) - t) * joint w t i := by
  rw [mollify_eq_integral]
  have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm (kernel_smul_integrable n hw (σ, y))
  simpa using this.symm

theorem kernel_component_integrable (n : ℕ) {w : ℝ → Space → Space}
    (hw : LocallyIntegrable (joint w) volume) (x : ℝ × Space) (i : Fin 3) :
    Integrable (fun t => kernel n (x - t) * joint w t i) volume := by
  have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integrable_comp (kernel_smul_integrable n hw x)
  simpa using this

end Internal.SmoothApprox

end Coercive

end Breakdown
