import Breakdown.Weak.StatementsTime
import Breakdown.Weak.AdvectionByParts
import Breakdown.FreqTr.PairingByParts

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.SliceIntegrand

theorem integrable_inner_loc {F G : Space → Space} (hF : LocallyIntegrable F volume)
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    Integrable (fun y => inner ℝ (F y) (G y)) volume := by
  have h1 : Integrable (fun y => ‖G y‖ • F y) volume :=
    hF.integrable_smul_left_of_hasCompactSupport hG.norm hGc.norm
  refine h1.norm.mono' (hF.aestronglyMeasurable.inner hG.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [norm_smul, norm_norm, Real.norm_eq_abs]
  calc |inner ℝ (F y) (G y)| ≤ ‖F y‖ * ‖G y‖ := abs_real_inner_le_norm _ _
    _ = ‖G y‖ * ‖F y‖ := mul_comm _ _

theorem fderiv_scaled {N : Space → Space} (hN : Differentiable ℝ N) (c b : ℝ) (y v : Space) :
    fderiv ℝ (fun z : Space => c • N (b • z)) y v = (c * b) • fderiv ℝ N (b • y) v := by
  have h : HasFDerivAt (fun z : Space => c • N (b • z))
      (c • ((fderiv ℝ N (b • y)).comp (b • ContinuousLinearMap.id ℝ Space))) y :=
    ((hN (b • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul b)).const_smul c
  rw [h.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul]

theorem spaceScale_eq (b : ℝ) (φ : Space → Space) :
    spaceScale b φ = fun z => (1 : ℝ) • φ (b • z) := by
  funext z
  simp [spaceScale]

theorem isTestField_scale {φ : Space → Space} (hφ : IsTestField φ) {b : ℝ} (hb : b ≠ 0) :
    IsTestField (spaceScale b φ) := by
  have hd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  refine ⟨hφ.1.comp (contDiff_id.const_smul b), hφ.2.1.comp_smul hb, fun y => ?_⟩
  have h0 := hφ.2.2 (b • y)
  rw [spaceScale_eq]
  simp only [divergenceAt] at h0 ⊢
  simp only [fderiv_scaled hd, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h0, mul_zero]

theorem partial_scaled {N : Space → Space} (hN : Differentiable ℝ N) (c b : ℝ) (j : Fin 3) :
    partialField (fun z => c • N (b • z)) j = fun x => (c * b) • partialField N j (b • x) :=
  funext fun x => fderiv_scaled hN c b x (unitVector j)

theorem negSsp_scaled {N : Space → Space} (hN : ContDiff ℝ ∞ N) (c b : ℝ) :
    negSsp (fun z => c • N (b • z)) = fun x => (c * b * b) • negSsp N (b • x) := by
  have hd : ∀ {g : Space → Space}, ContDiff ℝ ∞ g → Differentiable ℝ g :=
    fun hg => hg.differentiable (by simp)
  have hs : ContDiff ℝ ∞ (fun z => c • N (b • z)) :=
    (hN.comp (contDiff_id.const_smul b)).const_smul c
  have key : ∀ j, partialField (partialField (fun z => c • N (b • z)) j) j =
      fun x => (c * b * b) • partialField (partialField N j) j (b • x) := by
    intro j
    rw [partial_scaled (hd hN), partial_scaled (hd (Internal.WeakInX.smooth_partial hN j))]
  rw [Internal.WeakInX.negSsp_eq hs, Internal.WeakInX.negSsp_eq hN]
  funext x
  simp only [key, Finset.smul_sum, smul_neg]

theorem hasDerivAt_scale (s₀ σ : ℝ) :
    HasDerivAt (similarityScale s₀) (similarityScale s₀ σ * (-1 / 2)) σ := by
  unfold similarityScale
  exact (((hasDerivAt_id' σ).sub_const s₀).neg.div_const 2).exp

theorem deriv_scaledTest {α : ℝ → ℝ} (hα : Differentiable ℝ α) {φ : Space → Space}
    (hN : Differentiable ℝ (negSsp φ)) (s₀ σ : ℝ) (y : Space) :
    deriv (fun t => scaledTest α s₀ φ t y) σ =
      (α σ * similarityScale s₀ σ ^ 2) •
          fderiv ℝ (negSsp φ) (similarityScale s₀ σ • y) ((similarityScale s₀ σ * (-1 / 2)) • y) +
        (deriv α σ * similarityScale s₀ σ ^ 2 - α σ * similarityScale s₀ σ ^ 2) •
          negSsp φ (similarityScale s₀ σ • y) := by
  have hb := hasDerivAt_scale s₀ σ
  have hc := (hα σ).hasDerivAt.mul (hb.pow 2)
  have hcurve : HasDerivAt (fun t => negSsp φ (similarityScale s₀ t • y))
      (fderiv ℝ (negSsp φ) (similarityScale s₀ σ • y) ((similarityScale s₀ σ * (-1 / 2)) • y)) σ :=
    HasFDerivAt.comp_hasDerivAt (l := negSsp φ) (f := fun t => similarityScale s₀ t • y) σ
      (hN (similarityScale s₀ σ • y)).hasFDerivAt (hb.smul_const y)
  have h := hc.smul hcurve
  unfold scaledTest
  refine h.deriv.trans ?_
  congr 1
  congr 1
  norm_num
  ring

theorem pointwise {α : ℝ → ℝ} (hα : Differentiable ℝ α) {φ : Space → Space} (hφ : IsTestField φ)
    (s₀ σ : ℝ) (f : Space → Space) (g : Space → (Space →L[ℝ] Space)) (y : Space) :
    weakSimilarityIntegrand (fun _ => f) (fun _ => g) (scaledTest α s₀ φ) (σ, y) =
      -deriv α σ * inner ℝ (f y) (negSsp (spaceScale (similarityScale s₀ σ) φ) y) +
        α σ * ∑ i : Fin 3, inner ℝ (g y (unitVector i))
          (fderiv ℝ (negSsp (spaceScale (similarityScale s₀ σ) φ)) y (unitVector i)) -
        α σ * ∑ i : Fin 3, f y i * inner ℝ (f y)
          (fderiv ℝ (negSsp (spaceScale (similarityScale s₀ σ) φ)) y (unitVector i)) := by
  have hNs := (isTestField_negSsp hφ).1
  have hNd : Differentiable ℝ (negSsp φ) := hNs.differentiable (by simp)
  have e3 : negSsp (spaceScale (similarityScale s₀ σ) φ) = fun x =>
      (1 * similarityScale s₀ σ * similarityScale s₀ σ) • negSsp φ (similarityScale s₀ σ • x) := by
    rw [spaceScale_eq]
    exact negSsp_scaled hφ.1 1 _
  have e4 : ∀ v, fderiv ℝ (negSsp (spaceScale (similarityScale s₀ σ) φ)) y v =
      (1 * similarityScale s₀ σ * similarityScale s₀ σ * similarityScale s₀ σ) •
        fderiv ℝ (negSsp φ) (similarityScale s₀ σ • y) v := by
    intro v
    rw [e3]
    exact fderiv_scaled hNd _ _ y v
  have e2 : ∀ v, fderiv ℝ (scaledTest α s₀ φ σ) y v =
      (α σ * similarityScale s₀ σ ^ 2 * similarityScale s₀ σ) •
        fderiv ℝ (negSsp φ) (similarityScale s₀ σ • y) v :=
    fun v => fderiv_scaled hNd _ _ y v
  have e1 := deriv_scaledTest hα hNd s₀ σ y
  have e5 : scaledTest α s₀ φ σ y =
      (α σ * similarityScale s₀ σ ^ 2) • negSsp φ (similarityScale s₀ σ • y) := rfl
  unfold weakSimilarityIntegrand
  simp only [e1, e2, e4, e5]
  rw [e3]
  simp only [map_smul, inner_add_right, inner_smul_right, Fin.sum_univ_three]
  ring

theorem partial_pairing (hPV : PairingVelocity) (x : X) {M : Space → Space} (hM : IsTestField M) :
    ∫ y, ∑ i : Fin 3, inner ℝ ((partialX i x : Space → Space) y) (fderiv ℝ M y (unitVector i)) =
      inner ℝ x (embedX M) := by
  have hd : ∀ i : Fin 3, Continuous (fun y => fderiv ℝ M y (unitVector i)) := fun i =>
    (hM.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc : ∀ i : Fin 3, HasCompactSupport (fun y => fderiv ℝ M y (unitVector i)) := fun i =>
    hM.2.1.fderiv_apply (𝕜 := ℝ) (unitVector i)
  have hm : ∀ i : Fin 3, MemLp (fun y => fderiv ℝ M y (unitVector i)) 2 volume := fun i =>
    (hd i).memLp_of_hasCompactSupport (hc i)
  have hint : ∀ (z : X) (i : Fin 3), Integrable (fun y =>
      inner ℝ ((partialX i z : Space → Space) y) (fderiv ℝ M y (unitVector i))) volume :=
    fun z i => integrable_inner_loc ((Lp.memLp (partialX i z)).locallyIntegrable (by norm_num))
      (hd i) (hc i)
  have hL2 : ∀ (z : X) (i : Fin 3), ∫ y, inner ℝ ((partialX i z : Space → Space) y)
      (fderiv ℝ M y (unitVector i)) = inner ℝ (partialX i z) ((hm i).toLp _) := by
    intro z i
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hm i).coeFn_toLp] with y hy
    rw [hy]
  have hsplit : ∀ z : X, ∫ y, ∑ i : Fin 3, inner ℝ ((partialX i z : Space → Space) y)
      (fderiv ℝ M y (unitVector i)) = ∑ i : Fin 3, inner ℝ (partialX i z) ((hm i).toLp _) := by
    intro z
    rw [integral_finsetSum _ (fun i _ => hint z i)]
    exact Finset.sum_congr rfl fun i _ => hL2 z i
  rw [hsplit]
  have hcont : Continuous (fun z : X => ∑ i : Fin 3, inner ℝ (partialX i z) ((hm i).toLp _)) :=
    continuous_finsetSum _ fun i _ => ((partialX i).continuous.inner continuous_const)
  have heq : (fun z : X => ∑ i : Fin 3, inner ℝ (partialX i z) ((hm i).toLp _)) =
      fun z => inner ℝ z (embedX M) := by
    apply Continuous.ext_on testDense_holds.2 hcont (continuous_id.inner continuous_const)
    intro z hz
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds z hz
    have hdψ := isDecayField_of_isTestField hψ
    show ∑ i : Fin 3, inner ℝ (partialX i (embedX ψ)) ((hm i).toLp _) =
      inner ℝ (embedX ψ) (embedX M)
    rw [← hsplit, hPV _ M hM]
    have hall : ∀ᵐ y ∂volume, ∀ i : Fin 3,
        (partialX i (embedX ψ) : Space → Space) y = partialField ψ i y :=
      ae_all_iff.2 fun i => partial_holds.1 ψ hdψ i
    have e1 : (fun y => ∑ i : Fin 3, inner ℝ ((partialX i (embedX ψ) : Space → Space) y)
        (fderiv ℝ M y (unitVector i))) =ᵐ[volume]
        fun y => ∑ i : Fin 3, inner ℝ (fderiv ℝ ψ y (unitVector i)) (fderiv ℝ M y (unitVector i)) := by
      filter_upwards [hall] with y hy
      simp only [hy, partialField]
    have e2 : (fun y => inner ℝ ((velocity (embedX ψ) : Space → Space) y) (negSsp M y))
        =ᵐ[volume] fun y => inner ℝ (ψ y) (negSsp M y) := by
      filter_upwards [velocityDecay_holds ψ hdψ] with y hy
      rw [hy]
    rw [integral_congr_ae e1, integral_congr_ae e2]
    exact pairingByParts ψ M hdψ hM
  exact congrFun heq x

end Internal.SliceIntegrand

open Internal.SliceIntegrand in
theorem sliceIntegrand_holds : SliceIntegrand := by
  intro hPV hAd w f g C _hS hv hg α s₀ σ φ hα _hαc hφ
  have hαd : Differentiable ℝ α := hα.differentiable (by simp)
  have hβ : similarityScale s₀ σ ≠ 0 := (Real.exp_pos _).ne'
  have hχ := isTestField_scale hφ hβ
  have hM := isTestField_negSsp hχ
  obtain ⟨K, hK⟩ := Internal.AdvectionByParts.pairForm_bound hM
  have hall : ∀ᵐ y ∂volume, f y = (velocity w : Space → Space) y ∧
      ∀ i : Fin 3, g y (unitVector i) = (partialX i w : Space → Space) y := by
    filter_upwards [hv, ae_all_iff.2 hg] with y h1 h2
    exact ⟨h1.symm, fun i => (h2 i).symm⟩
  have hae : (fun y => weakSimilarityIntegrand (fun _ => f) (fun _ => g) (scaledTest α s₀ φ) (σ, y))
      =ᵐ[volume] fun y =>
        -deriv α σ * inner ℝ ((velocity w : Space → Space) y)
            (negSsp (spaceScale (similarityScale s₀ σ) φ) y) +
          α σ * ∑ i : Fin 3, inner ℝ ((partialX i w : Space → Space) y)
            (fderiv ℝ (negSsp (spaceScale (similarityScale s₀ σ) φ)) y (unitVector i)) -
          α σ * Internal.AdvectionByParts.pairForm (negSsp (spaceScale (similarityScale s₀ σ) φ))
            (velocity w) (velocity w) y := by
    filter_upwards [hall] with y hy
    rw [pointwise hαd hφ s₀ σ f g y, hy.1]
    simp only [hy.2, Internal.AdvectionByParts.pairForm]
  rw [integral_congr_ae hae]
  have i1 : Integrable (fun y => inner ℝ ((velocity w : Space → Space) y)
      (negSsp (spaceScale (similarityScale s₀ σ) φ) y)) volume :=
    integrable_inner_loc ((Lp.memLp (velocity w)).locallyIntegrable (by norm_num))
      hM.1.continuous hM.2.1
  have i2 : Integrable (fun y => ∑ i : Fin 3, inner ℝ ((partialX i w : Space → Space) y)
      (fderiv ℝ (negSsp (spaceScale (similarityScale s₀ σ) φ)) y (unitVector i))) volume :=
    integrable_finsetSum _ fun i _ => integrable_inner_loc
      ((Lp.memLp (partialX i w)).locallyIntegrable (by norm_num))
      ((hM.1.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hM.2.1.fderiv_apply (𝕜 := ℝ) _)
  have i3 := (hK (velocity w) (velocity w)).1
  have h5 : ∫ y, Internal.AdvectionByParts.pairForm (negSsp (spaceScale (similarityScale s₀ σ) φ))
      (velocity w) (velocity w) y = -trilinear w w (negSsp (spaceScale (similarityScale s₀ σ) φ)) :=
    hAd w _ hM
  have j1 : Integrable (fun y => -deriv α σ * inner ℝ ((velocity w : Space → Space) y)
      (negSsp (spaceScale (similarityScale s₀ σ) φ) y)) volume := i1.const_mul _
  have j2 : Integrable (fun y => α σ * ∑ i : Fin 3, inner ℝ ((partialX i w : Space → Space) y)
      (fderiv ℝ (negSsp (spaceScale (similarityScale s₀ σ) φ)) y (unitVector i))) volume :=
    i2.const_mul _
  have j3 : Integrable (fun y => α σ * Internal.AdvectionByParts.pairForm
      (negSsp (spaceScale (similarityScale s₀ σ) φ)) (velocity w) (velocity w) y) volume :=
    i3.const_mul _
  have j12 : Integrable (fun y => -deriv α σ * inner ℝ ((velocity w : Space → Space) y)
      (negSsp (spaceScale (similarityScale s₀ σ) φ) y) +
        α σ * ∑ i : Fin 3, inner ℝ ((partialX i w : Space → Space) y)
          (fderiv ℝ (negSsp (spaceScale (similarityScale s₀ σ) φ)) y (unitVector i))) volume :=
    j1.add j2
  rw [integral_sub j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul, ← hPV w _ hχ, partial_pairing hPV w hM, h5]
  unfold similarityRate weakRate
  ring

end Breakdown.WeakProfile
