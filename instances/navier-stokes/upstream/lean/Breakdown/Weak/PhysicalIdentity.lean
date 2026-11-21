import Breakdown.Weak.StatementsTime
import Breakdown.FreqTr.WeakInX
import Breakdown.FreqTr.EmbedDilate

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.PhysicalIdentity

theorem scale_pos (s₀ σ : ℝ) : 0 < similarityScale s₀ σ := Real.exp_pos _

theorem scale_sq (s₀ σ : ℝ) : similarityScale s₀ σ ^ 2 = Real.exp (-(σ - s₀)) := by
  rw [similarityScale, ← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem continuous_scale (s₀ : ℝ) : Continuous (similarityScale s₀) := by
  unfold similarityScale; fun_prop

def timeChange (s₀ σ : ℝ) : ℝ := 1 - Real.exp (-(σ - s₀))

theorem hasDerivAt_timeChange (s₀ σ : ℝ) :
    HasDerivAt (timeChange s₀) (similarityScale s₀ σ ^ 2) σ := by
  rw [scale_sq]
  exact ((((hasDerivAt_id σ).sub_const s₀).neg.exp).const_sub 1).congr_deriv (by simp)

theorem timeChange_injective (s₀ : ℝ) : Function.Injective (timeChange s₀) := by
  intro a b h
  simp only [timeChange, sub_right_inj] at h
  have := Real.exp_injective h
  linarith

theorem image_timeChange (s₀ : ℝ) : timeChange s₀ '' univ = Iio 1 := by
  ext t
  simp only [image_univ, mem_range, mem_Iio, timeChange]
  constructor
  · rintro ⟨σ, rfl⟩
    linarith [Real.exp_pos (-(σ - s₀))]
  · intro ht
    refine ⟨s₀ - Real.log (1 - t), ?_⟩
    have e : -(s₀ - Real.log (1 - t) - s₀) = Real.log (1 - t) := by ring
    rw [e, Real.exp_log (by linarith)]
    ring

theorem one_sub_timeChange (s₀ σ : ℝ) : 1 - timeChange s₀ σ = similarityScale s₀ σ ^ 2 := by
  rw [scale_sq, timeChange]; ring

theorem sqrt_inv_timeChange (s₀ σ : ℝ) :
    (Real.sqrt (1 - timeChange s₀ σ)⁻¹)⁻¹ = similarityScale s₀ σ := by
  rw [one_sub_timeChange, ← inv_pow, Real.sqrt_sq (inv_nonneg.2 (scale_pos s₀ σ).le), inv_inv]

theorem inv_timeChange_pos (s₀ σ : ℝ) : 0 < (1 - timeChange s₀ σ)⁻¹ := by
  rw [one_sub_timeChange]; exact inv_pos.2 (pow_pos (scale_pos s₀ σ) 2)

theorem curve_timeChange (x : ℝ → X) (s₀ σ : ℝ) :
    physicalCurve x s₀ (timeChange s₀ σ) = dilX (1 - timeChange s₀ σ)⁻¹ (x σ) := by
  have e : s₀ - Real.log (1 - timeChange s₀ σ) = σ := by
    rw [timeChange, sub_sub_cancel, Real.log_exp]; ring
  unfold physicalCurve
  rw [e]

theorem isTestField_spaceScale {b : ℝ} (hb : b ≠ 0) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (spaceScale b φ) := by
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨h1.comp (contDiff_id.const_smul b), ?_, ?_⟩
  · exact h2.comp_homeomorph (Homeomorph.smulOfNeZero b hb)
  · intro y
    have hd : HasFDerivAt (spaceScale b φ)
        ((fderiv ℝ φ (b • y)).comp (b • ContinuousLinearMap.id ℝ Space)) y :=
      ((h1.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y
        ((hasFDerivAt_id y).const_smul b)
    have h0 := h3 (b • y)
    simp only [divergenceAt] at h0 ⊢
    simp only [hd.fderiv, ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h0,
      mul_zero]

theorem negSsp_spaceScale (b : ℝ) {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) :
    negSsp (spaceScale b φ) = (b ^ 2) • spaceScale b (negSsp φ) := by
  funext y
  have key : ∀ v : Space, iteratedFDeriv ℝ 2 (spaceScale b φ) y ![v, v] =
      b ^ 2 • iteratedFDeriv ℝ 2 φ (b • y) ![v, v] := by
    intro v
    have h := (b • ContinuousLinearMap.id ℝ Space).iteratedFDeriv_comp_right hφ y (i := 2) (by exact_mod_cast ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have e : spaceScale b φ = φ ∘ (b • ContinuousLinearMap.id ℝ Space) := rfl
    rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have e2 : (fun i => (b • ContinuousLinearMap.id ℝ Space) (![v, v] i)) =
        fun i => (fun _ => b) i • ![v, v] i := by
      funext i; simp
    rw [e2, ContinuousMultilinearMap.map_smul_univ]
    simp
  show -sumSecondPartialsAt (spaceScale b φ) y = b ^ 2 • (-sumSecondPartialsAt φ (b • y))
  simp only [sumSecondPartialsAt, key, ← Finset.smul_sum, smul_neg]

theorem trilinear_smul (u v : X) (c : ℝ) (w : Space → Space) :
    trilinear u v (c • w) = c * trilinear u v w := by
  unfold trilinear
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.smul_apply, real_inner_smul_right]
  ring

theorem pairing_timeChange (hPV : PairingVelocity) (hPD : PairingDilate) (x : ℝ → X) (s₀ σ : ℝ)
    {ψ : Space → Space} (hψ : IsTestField ψ) :
    inner ℝ (physicalCurve x s₀ (timeChange s₀ σ)) (embedX ψ) =
      inner ℝ (x σ) (embedX (spaceScale (similarityScale s₀ σ) ψ)) := by
  rw [curve_timeChange, hPD hPV _ (inv_timeChange_pos s₀ σ) (x σ) ψ hψ, sqrt_inv_timeChange]

theorem trilinear_timeChange (hVW : VelocityWeakGradient) (hTD : TrilinearDilate) (x : ℝ → X)
    (s₀ σ : ℝ) {ψ : Space → Space} (hψ : IsTestField ψ) :
    trilinear (physicalCurve x s₀ (timeChange s₀ σ)) (physicalCurve x s₀ (timeChange s₀ σ)) ψ =
      trilinear (x σ) (x σ) (spaceScale (similarityScale s₀ σ) ψ) := by
  rw [curve_timeChange, hTD hVW _ (inv_timeChange_pos s₀ σ) (x σ) ψ hψ, sqrt_inv_timeChange]

theorem weakRate_timeChange (hPV : PairingVelocity) (hVW : VelocityWeakGradient)
    (hPD : PairingDilate) (hTD : TrilinearDilate) (x : ℝ → X) (s₀ σ : ℝ)
    {φ : Space → Space} (hφ : IsTestField φ) :
    similarityScale s₀ σ ^ 2 * weakRate (physicalCurve x s₀ (timeChange s₀ σ)) φ =
      weakRate (x σ) (spaceScale (similarityScale s₀ σ) φ) := by
  have hb := scale_pos s₀ σ
  have hl := Freq.isTestField_negSsp hφ
  have hs := isTestField_spaceScale hb.ne' hl
  unfold weakRate
  rw [pairing_timeChange hPV hPD x s₀ σ hl, trilinear_timeChange hVW hTD x s₀ σ hl,
    negSsp_spaceScale _ hφ.1,
    embedNormLinear_holds.2.2.2 _ _ (Freq.isDecayField_of_isTestField hs),
    real_inner_smul_right, trilinear_smul]
  ring

theorem embedX_spaceScale {b : ℝ} (hb : 0 < b) {φ : Space → Space} (hφ : IsTestField φ) :
    embedX (spaceScale b φ) = b⁻¹ • dilX (b ^ 2) (embedX φ) := by
  have hs := isTestField_spaceScale hb.ne' hφ
  have e : dilateField (b ^ 2) φ = b • spaceScale b φ := by
    funext y
    simp [dilateField, spaceScale, Real.sqrt_sq hb.le]
  rw [embedDilate fieldOpRealized_holds dilation_holds embedMem_holds _ _ (pow_pos hb 2)
      (Freq.isDecayField_of_isTestField hφ), e,
    embedNormLinear_holds.2.2.2 _ _ (Freq.isDecayField_of_isTestField hs),
    smul_smul, inv_mul_cancel₀ hb.ne', one_smul]

theorem continuous_embedX_spaceScale (s₀ : ℝ) {φ : Space → Space} (hφ : IsTestField φ) :
    Continuous (fun σ => embedX (spaceScale (similarityScale s₀ σ) φ)) := by
  have e : (fun σ => embedX (spaceScale (similarityScale s₀ σ) φ)) =
      fun σ => (similarityScale s₀ σ)⁻¹ • dilX (similarityScale s₀ σ ^ 2) (embedX φ) := by
    funext σ; exact embedX_spaceScale (scale_pos s₀ σ) hφ
  rw [e]
  have hc := continuous_scale s₀
  refine (hc.inv₀ (fun σ => (scale_pos s₀ σ).ne')).smul ?_
  exact (dilationCont_holds (embedX φ)).comp_continuous (hc.pow 2)
    (fun σ => pow_pos (scale_pos s₀ σ) 2)

theorem exists_lt_one {K : Set ℝ} (hK : IsCompact K) (hs : K ⊆ Ioo (-1) 1) :
    ∃ c < 1, ∀ t ∈ K, t ≤ c := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨0, by norm_num, by simp [h]⟩
  · exact ⟨sSup K, (hs (hK.sSup_mem h)).2, fun t ht => le_csSup hK.bddAbove ht⟩

end Internal.PhysicalIdentity

open Internal.PhysicalIdentity in
theorem physicalIdentity_of_parts (hPV : PairingVelocity) (hVW : VelocityWeakGradient) :
    PhysicalIdentity := by
  intro hPD hTD x M s₀ hM hxm hsim θ φ hθ hθc hθs hφ
  have cov : ∀ g : ℝ → ℝ, (∀ t, 1 ≤ t → g t = 0) →
      ∫ t, g t = ∫ σ, similarityScale s₀ σ ^ 2 * g (timeChange s₀ σ) := by
    intro g hg
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iio 1)
        (fun t ht => hg t (not_lt.1 ht)), ← image_timeChange s₀,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun σ _ => (hasDerivAt_timeChange s₀ σ).hasDerivWithinAt)
        (timeChange_injective s₀).injOn, Measure.restrict_univ]
    congr 1
    funext σ
    rw [abs_of_nonneg (by positivity), smul_eq_mul]
  have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hα : ContDiff ℝ ∞ (fun σ => θ (timeChange s₀ σ)) := by
    unfold timeChange
    exact hθ.comp (contDiff_const.sub (contDiff_id.sub contDiff_const).neg.exp)
  obtain ⟨c, hc1, hcK⟩ := exists_lt_one hθc hθs
  have hαc : HasCompactSupport (fun σ => θ (timeChange s₀ σ)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := s₀ - Real.log 2)
      (b := s₀ - Real.log (1 - c))) ?_
    intro σ hσ
    by_contra hne
    have hmem : timeChange s₀ σ ∈ tsupport θ := subset_tsupport _ hne
    have h1 := (hθs hmem).1
    have h2 := hcK _ hmem
    apply hσ
    simp only [timeChange] at h1 h2
    have e := Real.exp_pos (-(σ - s₀))
    constructor
    · have h3 : Real.exp (-(σ - s₀)) < 2 := by linarith
      have h4 := Real.log_lt_log e h3
      rw [Real.log_exp] at h4
      linarith
    · have h3 : 1 - c ≤ Real.exp (-(σ - s₀)) := by linarith
      have h4 := Real.log_le_log (by linarith) h3
      rw [Real.log_exp] at h4
      linarith
  have hder : ∀ σ, deriv (fun σ => θ (timeChange s₀ σ)) σ =
      deriv θ (timeChange s₀ σ) * similarityScale s₀ σ ^ 2 := fun σ =>
    ((hθd _).hasDerivAt.comp σ (hasDerivAt_timeChange s₀ σ)).deriv
  obtain ⟨hint, hzero⟩ := hsim _ φ hα hαc hφ
  have hw : Continuous (fun σ => deriv (fun σ => θ (timeChange s₀ σ)) σ •
      embedX (spaceScale (similarityScale s₀ σ) φ)) :=
    (hα.continuous_deriv (by simp)).smul (continuous_embedX_spaceScale s₀ hφ)
  have hwc : HasCompactSupport (fun σ => deriv (fun σ => θ (timeChange s₀ σ)) σ •
      embedX (spaceScale (similarityScale s₀ σ) φ)) := hαc.deriv.smul_right
  have hIP' : Integrable (fun σ => inner ℝ (x σ)
      (deriv (fun σ => θ (timeChange s₀ σ)) σ • embedX (spaceScale (similarityScale s₀ σ) φ))) := by
    refine Integrable.mono' ((hw.integrable_of_hasCompactSupport hwc).norm.const_mul M)
      (hxm.inner hw.aestronglyMeasurable) (ae_of_all _ (fun σ => ?_))
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM σ) (norm_nonneg _))
  have hIP : Integrable (fun σ => deriv (fun σ => θ (timeChange s₀ σ)) σ *
      inner ℝ (x σ) (embedX (spaceScale (similarityScale s₀ σ) φ))) := by
    refine hIP'.congr (ae_of_all _ (fun σ => ?_))
    exact real_inner_smul_right _ _ _
  rw [cov (fun t => deriv θ t * inner ℝ (physicalCurve x s₀ t) (embedX φ)) (fun t ht => by
      have : deriv θ t = 0 := by
        by_contra h
        exact absurd (hθs (support_deriv_subset h)).2 (not_lt.2 ht)
      simp [this]),
    cov (fun t => θ t * weakRate (physicalCurve x s₀ t) φ) (fun t ht => by
      have : θ t = 0 := image_eq_zero_of_notMem_tsupport (fun h => absurd (hθs h).2 (not_lt.2 ht))
      simp [this])]
  have e1 : (fun σ => similarityScale s₀ σ ^ 2 * (deriv θ (timeChange s₀ σ) *
      inner ℝ (physicalCurve x s₀ (timeChange s₀ σ)) (embedX φ))) =
      fun σ => deriv (fun σ => θ (timeChange s₀ σ)) σ *
        inner ℝ (x σ) (embedX (spaceScale (similarityScale s₀ σ) φ)) := by
    funext σ
    rw [hder, pairing_timeChange hPV hPD x s₀ σ hφ]
    ring
  have e2 : (fun σ => similarityScale s₀ σ ^ 2 * (θ (timeChange s₀ σ) *
      weakRate (physicalCurve x s₀ (timeChange s₀ σ)) φ)) =
      fun σ => similarityRate x (fun σ => θ (timeChange s₀ σ)) s₀ φ σ +
        deriv (fun σ => θ (timeChange s₀ σ)) σ *
          inner ℝ (x σ) (embedX (spaceScale (similarityScale s₀ σ) φ)) := by
    funext σ
    rw [similarityRate, ← weakRate_timeChange hPV hVW hPD hTD x s₀ σ hφ]
    ring
  rw [e1, e2, integral_add hint hIP, hzero, zero_add]

end Breakdown.WeakProfile
