import Breakdown.Cert.CoerciveSmoothApproxIterated

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem convolution_fderiv_apply_of {ψ : ℝ × Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ × Space → E} (hf : LocallyIntegrable f volume) (x w : ℝ × Space) :
    fderiv ℝ (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x w =
      ((fun t => fderiv ℝ ψ t w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  have := volume_prod_invariantClass
  have hd := hc.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (hψ.of_le (by exact_mod_cast le_top)) hf x
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ℝ × Space)) (hψ.continuous_fderiv (by simp)) hf x
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
  simp

theorem shift_hasCompactSupport {ψ : ℝ × Space → ℝ} (hc : HasCompactSupport ψ) (σ s : ℝ) (y : Space) :
    HasCompactSupport (fun z : Space => ψ ((σ, y) - (s, z))) := by
  refine HasCompactSupport.intro (((hc.isCompact.image continuous_snd).image
    (continuous_const.sub continuous_id : Continuous fun w : Space => y - w))) ?_
  intro z hz
  by_contra h0
  apply hz
  refine ⟨y - z, ⟨(σ, y) - (s, z), subset_tsupport _ h0, by simp⟩, by simp⟩

theorem shift_fderiv_of {ψ : ℝ × Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (σ s : ℝ) (y z e : Space) :
    fderiv ℝ (fun z : Space => ψ ((σ, y) - (s, z))) z e = -fderiv ℝ ψ ((σ, y) - (s, z)) (0, e) := by
  have hk : DifferentiableAt ℝ ψ ((σ, y) - (s, z)) := hψ.differentiable (by simp) _
  have h1 : HasFDerivAt (fun z : Space => ψ ((σ, y) - (s, z)))
      ((fderiv ℝ ψ ((σ, y) - (s, z))).comp (-(ContinuousLinearMap.inr ℝ ℝ Space))) z := by
    have hin : HasFDerivAt (fun z : Space => (σ, y) - (s, z))
        (-(ContinuousLinearMap.inr ℝ ℝ Space)) z := by
      have := ((hasFDerivAt_prodMk_right (𝕜 := ℝ) s z).const_sub (σ, y))
      simpa using this
    exact hk.hasFDerivAt.comp z hin
  rw [h1.fderiv]
  simp

theorem partial_eq_of {ψ : ℝ × Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {v Gc : ℝ → Space → Space}
    (hv : LocallyIntegrable (joint v) volume) (hG : LocallyIntegrable (joint Gc) volume) (i : Fin 3)
    (hw : ∀ᵐ s, ∀ φ, IsTestFunction φ →
      ∫ z, φ z • Gc s z = -∫ z, fderiv ℝ φ z (unitVector i) • v s z) (σ : ℝ) (y : Space) :
    ((fun t => fderiv ℝ ψ t (0, unitVector i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      joint v) (σ, y) = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint Gc) (σ, y) := by
  have := volume_prod_invariantClass
  set x : ℝ × Space := (σ, y)
  have hc1 : Continuous (fun t => fderiv ℝ ψ (x - t) (0, unitVector i)) :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
      (continuous_const.sub continuous_id)
  have hs1 : HasCompactSupport (fun t => fderiv ℝ ψ (x - t) (0, unitVector i)) :=
    (hc.fderiv_apply (𝕜 := ℝ) (0, unitVector i)).comp_homeomorph (Homeomorph.subLeft x)
  have hc2 : Continuous (fun t => ψ (x - t)) := hψ.continuous.comp (continuous_const.sub continuous_id)
  have hs2 : HasCompactSupport (fun t => ψ (x - t)) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have i1 := hv.integrable_smul_left_of_hasCompactSupport hc1 hs1
  have i2 := hG.integrable_smul_left_of_hasCompactSupport hc2 hs2
  rw [convolution_eq_swap, convolution_eq_swap]
  try simp only [ContinuousLinearMap.lsmul_apply]
  rw [Measure.volume_eq_prod] at i1 i2 ⊢
  rw [integral_prod _ i1, integral_prod _ i2]
  refine integral_congr_ae ?_
  filter_upwards [hw] with s hs
  have e := hs (fun z : Space => ψ ((σ, y) - (s, z)))
    ⟨hψ.comp (contDiff_const.sub (contDiff_const.prodMk contDiff_id)), shift_hasCompactSupport hc σ s y⟩
  simp only [shift_fderiv_of hψ, neg_smul, integral_neg, neg_neg] at e
  simpa [joint, x] using e.symm

theorem slice_fderiv_clm_of {ψ : ℝ × Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {f : ℝ → Space → Space} {F : ℝ → Space → (Space →L[ℝ] Space)}
    (hf : LocallyIntegrable (joint f) volume) (hF : LocallyIntegrable (joint F) volume)
    (hw : ∀ᵐ s, IsWeakGradient (f s) (F s)) (σ : ℝ) :
    fderiv ℝ (fun y => (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint f) (σ, y)) =
      fun y => (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint F) (σ, y) := by
  have := volume_prod_invariantClass
  funext y
  have hdiff : DifferentiableAt ℝ (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint f) (σ, y) :=
    (hc.contDiff_convolution_left _ hψ hf).differentiable (by simp) (σ, y)
  have h1 : HasFDerivAt (fun y => (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint f) (σ, y))
      ((fderiv ℝ (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint f) (σ, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)
  rw [h1.fderiv]
  refine ContinuousLinearMap.coe_injective ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_)
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
  rw [convolution_fderiv_apply_of hψ hc hf]
  have h2 := partial_eq_of hψ hc hf (joint_apply_locallyIntegrable hF (unitVector i)) i
    (hw.mono fun s hs φ hφ => hs.2.2 φ hφ i) σ y
  simp only [unitVector] at h2
  rw [h2]
  have hex := (hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hψ.continuous hF) (σ, y)
  rw [convolution_def, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp [joint]

end Internal.SmoothApprox

end Coercive

end Breakdown
