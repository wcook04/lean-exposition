import Breakdown.Frac.StOperator

open MeasureTheory Real Module

noncomputable section

namespace Breakdown

namespace FracInternal

private lemma scalarCoordIsometry (ξ : Space) (hξ : ξ ≠ 0) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space, ∀ z : Space, inner ℝ z ξ = ‖ξ‖ * (R z) 0 := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  set u : Space := ‖ξ‖⁻¹ • ξ with hu_def
  set e : Space := EuclideanSpace.single 0 1 with he_def
  have hue : ‖u‖ = ‖e‖ := by
    simp [hu_def, he_def, norm_smul, hn]
  obtain ⟨ρ, hρu⟩ : ∃ ρ : Space ≃ₗᵢ[ℝ] Space, ρ u = e := ⟨_, Submodule.reflection_sub hue⟩
  refine ⟨ρ, fun z => ?_⟩
  have h1 : (ρ z) 0 = inner ℝ (ρ z) e := by
    simp [he_def, EuclideanSpace.inner_single_right]
  have h2 : inner ℝ (ρ z) e = inner ℝ z u := by
    rw [← hρu, LinearIsometryEquiv.inner_map_map]
  rw [h1, h2, hu_def, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

private lemma scalarCosRescale (α : ℝ) (ξ : Space) (hξ : ξ ≠ 0) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space, ∀ z : Space,
      ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2) =
        ‖ξ‖ ^ (3 + 2 * α) * (‖‖ξ‖ • R z‖ ^ (-(3 + 2 * α)) *
          (Real.cos ((‖ξ‖ • R z) 0) - 1 + ((‖ξ‖ • R z) 0) ^ 2 / 2)) := by
  obtain ⟨R, hR⟩ := scalarCoordIsometry ξ hξ
  refine ⟨R, fun z => ?_⟩
  have hc : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hone : ‖ξ‖ ^ (3 + 2 * α) * ‖ξ‖ ^ (-(3 + 2 * α)) = 1 := by
    rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero]
  rw [hR z, norm_smul, norm_norm, R.norm_map, PiLp.smul_apply, smul_eq_mul,
    Real.mul_rpow hc.le (norm_nonneg _), mul_assoc (‖ξ‖ ^ (-(3 + 2 * α))),
    ← mul_assoc (‖ξ‖ ^ (3 + 2 * α)), hone, one_mul]

private lemma scalarCosPart (h0 : NormalizerStatement) (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2)
    (ξ : Space) :
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2)) ∧
    ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2) =
      ‖ξ‖ ^ (2 * α) * fractionalNormalizer α := by
  obtain ⟨hint, -⟩ := h0 α h1 (by linarith)
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have hα : 2 * α ≠ 0 := by intro h; linarith
    simp [Real.zero_rpow hα]
  · obtain ⟨R, hR⟩ := scalarCosRescale α ξ hξ
    have hc : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    set H : Space → ℝ := fun v => ‖v‖ ^ (-(3 + 2 * α)) * (Real.cos (v 0) - 1 + (v 0) ^ 2 / 2)
      with hH
    have hfun : (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
        (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2)) =
        (fun w => ‖ξ‖ ^ (3 + 2 * α) * H (‖ξ‖ • w)) ∘ R := by
      funext z
      exact hR z
    have hmp := R.measurePreserving
    rw [hfun]
    refine ⟨hmp.integrable_comp_of_integrable ((hint.comp_smul hc.ne').const_mul _), ?_⟩
    rw [Function.comp_def, hmp.integral_comp R.toHomeomorph.measurableEmbedding
      (fun w => ‖ξ‖ ^ (3 + 2 * α) * H (‖ξ‖ • w))]
    rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin, smul_eq_mul,
      abs_of_pos (by positivity)]
    show _ = ‖ξ‖ ^ (2 * α) * ∫ x, H x
    have hsplit : ‖ξ‖ ^ (3 + 2 * α) = ‖ξ‖ ^ 3 * ‖ξ‖ ^ (2 * α) := by
      rw [Real.rpow_add hc, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : (‖ξ‖ ^ 3 : ℝ) ≠ 0 := by positivity
    rw [hsplit]
    field_simp

private lemma scalarSinCube (t : ℝ) : |Real.sin t - t| ≤ 2 * |t| ^ 3 := by
  rcases le_or_gt |t| 1 with ht | ht
  · have hb := Real.sin_bound ht
    have h5 : |t| ^ 5 ≤ |t| ^ 3 := pow_le_pow_of_le_one (abs_nonneg t) ht (by norm_num)
    have ht3 : |-(t ^ 3 / 6)| = |t| ^ 3 / 6 := by rw [abs_neg, abs_div, abs_pow]; norm_num
    calc |Real.sin t - t| = |(Real.sin t - (t - t ^ 3 / 6)) + (-(t ^ 3 / 6))| := by
          congr 1; ring
      _ ≤ |Real.sin t - (t - t ^ 3 / 6)| + |-(t ^ 3 / 6)| := abs_add_le _ _
      _ ≤ |t| ^ 5 / 100 + |t| ^ 3 / 6 := by rw [ht3]; linarith
      _ ≤ 2 * |t| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg t) 3]
  · have hs := Real.abs_sin_le_one t
    have h3 : |t| ≤ |t| ^ 3 := le_self_pow₀ ht.le (by norm_num)
    have htri : |Real.sin t - t| ≤ |Real.sin t| + |t| := by
      have := abs_add_le (Real.sin t) (-t)
      rwa [abs_neg, ← sub_eq_add_neg] at this
    linarith

private lemma scalarSinLin (t : ℝ) : |Real.sin t - t| ≤ 2 * |t| := by
  have hs : |Real.sin t| ≤ |t| := by
    simpa using Real.abs_sin_sub_sin_le t 0
  have htri : |Real.sin t - t| ≤ |Real.sin t| + |t| := by
    have := abs_add_le (Real.sin t) (-t)
    rwa [abs_neg, ← sub_eq_add_neg] at this
  linarith

private lemma scalarFarBound (x r : ℝ) (hx : 1 ≤ x) (hr : 0 ≤ r) :
    x ^ (-r) ≤ 2 ^ r * (1 + x) ^ (-r) := by
  have hle : (2 * x) ^ (-r) ≤ (1 + x) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have heq : x ^ (-r) = 2 ^ r * (2 * x) ^ (-r) := by
    rw [Real.mul_rpow (by norm_num) (by linarith), ← mul_assoc, ← Real.rpow_add (by norm_num),
      add_neg_cancel, Real.rpow_zero, one_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

private lemma scalarSinIntegrable (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2) (ξ : Space) :
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)) := by
  have hcont : Continuous (fun z : Space => Real.sin (inner ℝ z ξ) - inner ℝ z ξ) :=
    (Real.continuous_sin.comp (continuous_id.inner continuous_const)).sub
      (continuous_id.inner continuous_const)
  have hmeas : AEStronglyMeasurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)) volume :=
    ((measurable_norm.pow_const _).mul hcont.measurable).aestronglyMeasurable
  have hbound : ∀ z : Space, ‖‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)‖ ≤
      ‖z‖ ^ (-(3 + 2 * α)) * |Real.sin (inner ℝ z ξ) - inner ℝ z ξ| := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  have hin : ∀ z : Space, |inner ℝ z ξ| ≤ ‖z‖ * ‖ξ‖ := fun z => abs_real_inner_le_norm z ξ
  have hnear : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)) (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := 2 * ‖ξ‖ ^ 3) (α := 2 * α)
      (by simp) (by simp; linarith)
      (ae_of_all _ fun z => ?_) hmeas
    have key : ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ (3 : ℕ) = ‖z‖ ^ (-(2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg z) (by push_cast; intro h; linarith)]
      congr 1
      push_cast
      ring
    calc _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * |Real.sin (inner ℝ z ξ) - inner ℝ z ξ| := hbound z
      _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * (2 * (‖z‖ * ‖ξ‖) ^ 3) :=
          mul_le_mul_of_nonneg_left ((scalarSinCube _).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hin z) 3) (by norm_num)))
            (Real.rpow_nonneg (norm_nonneg z) _)
      _ = 2 * ‖ξ‖ ^ 3 * (‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ (3 : ℕ)) := by ring
      _ = 2 * ‖ξ‖ ^ 3 * ‖z‖ ^ (-(2 * α)) := by rw [key]
  have hfar : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)) (Metric.ball (0 : Space) 1)ᶜ volume := by
    have hr : (finrank ℝ Space : ℝ) < 2 + 2 * α := by
      simp; linarith
    have hg := ((integrable_one_add_norm (μ := (volume : Measure Space)) hr).const_mul
      (2 * ‖ξ‖ * 2 ^ (2 + 2 * α))).integrableOn (s := (Metric.ball (0 : Space) 1)ᶜ)
    refine hg.mono' hmeas.restrict
      (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet.compl fun z hz => ?_)
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hz0 : 0 < ‖z‖ := by linarith
    have hpow : ‖z‖ ^ (-(2 + 2 * α)) = ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ := by
      rw [show -(2 + 2 * α) = -(3 + 2 * α) + 1 by ring, Real.rpow_add hz0, Real.rpow_one]
    calc _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * |Real.sin (inner ℝ z ξ) - inner ℝ z ξ| := hbound z
      _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * (2 * (‖z‖ * ‖ξ‖)) :=
          mul_le_mul_of_nonneg_left ((scalarSinLin _).trans
            (mul_le_mul_of_nonneg_left (hin z) (by norm_num))) (Real.rpow_nonneg (norm_nonneg z) _)
      _ = 2 * ‖ξ‖ * ‖z‖ ^ (-(2 + 2 * α)) := by rw [hpow]; ring
      _ ≤ 2 * ‖ξ‖ * (2 ^ (2 + 2 * α) * (1 + ‖z‖) ^ (-(2 + 2 * α))) :=
          mul_le_mul_of_nonneg_left (scalarFarBound _ _ hz1 (by linarith)) (by positivity)
      _ = 2 * ‖ξ‖ * 2 ^ (2 + 2 * α) * (1 + ‖z‖) ^ (-(2 + 2 * α)) := by ring
  have hall := hnear.union hfar
  rwa [Set.union_compl_self, integrableOn_univ] at hall

private lemma scalarSinIntegral (α : ℝ) (ξ : Space) :
    ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ξ) - inner ℝ z ξ) = 0 := by
  set F : Space → ℝ := fun z => ‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)
    with hF
  have hodd : ∀ z, F (-z) = -F z := by
    intro z
    simp only [hF, norm_neg, inner_neg_left, Real.sin_neg]
    ring
  let N : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.neg ℝ
  have hN : ∀ z, N z = -z := fun z => rfl
  have h := N.measurePreserving.integral_comp N.toHomeomorph.measurableEmbedding F
  simp only [hN, hodd, integral_neg] at h
  linarith

end FracInternal

open FracInternal in
theorem symbolScalar (h0 : NormalizerStatement) : SymbolScalarStatement := by
  intro α h1 h2 ξ
  obtain ⟨hc1, hc2⟩ := scalarCosPart h0 α h1 h2 ξ
  exact ⟨hc1, hc2, scalarSinIntegrable α h1 h2 ξ, scalarSinIntegral α ξ⟩

end Breakdown
