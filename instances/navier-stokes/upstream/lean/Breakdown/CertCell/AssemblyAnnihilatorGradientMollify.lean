import Breakdown.Defs

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.CertCell.AnnihilatorGradient.Internal

def smulFlip : Space →L[ℝ] ℝ →L[ℝ] Space := (ContinuousLinearMap.lsmul ℝ ℝ).flip

def mollify (Q : Space → Space) (ρ : Space → ℝ) : Space → Space := convolution Q ρ smulFlip volume

theorem sum_coord (w : Space) : ∑ i, w i • unitVector i = w := by
  ext j
  simp [unitVector, Pi.single_apply]

theorem clm_sum_coord (c : Space →L[ℝ] ℝ) (w : Space) : ∑ i, c (unitVector i) * w i = c w := by
  conv_rhs => rw [← sum_coord w]
  simp [map_sum, map_smul, mul_comm]

theorem stationary_pair {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x u w : Space) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ ρ (x - t) u • w - fderiv ℝ ρ (x - t) w • u) ∧
    HasCompactSupport (fun t => fderiv ℝ ρ (x - t) u • w - fderiv ℝ ρ (x - t) w • u) ∧
    ∀ y, divergenceAt (fun t => fderiv ℝ ρ (x - t) u • w - fderiv ℝ ρ (x - t) w • u) y = 0 := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.fderiv_right (by simp)
  have hg : ∀ v : Space, ContDiff ℝ ∞ (fun t => fderiv ℝ ρ (x - t) v) := fun v =>
    (hd.comp (contDiff_const.sub contDiff_id)).clm_apply contDiff_const
  refine ⟨((hg u).smul contDiff_const).sub ((hg w).smul contDiff_const), ?_, ?_⟩
  · have hK : HasCompactSupport (fun t => fderiv ℝ ρ (x - t)) :=
      (hρc.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft x)
    refine hK.mono ?_
    intro t ht
    simp only [Function.mem_support] at ht ⊢
    intro h0
    apply ht
    simp [h0]
  · intro y
    set D2 := fderiv ℝ (fderiv ℝ ρ) (x - y) with hD2
    have hsym : ∀ a b, D2 a b = D2 b a := (hρ.contDiffAt).isSymmSndFDerivAt
      (by simp; norm_cast)
    have hD : ∀ v : Space, HasFDerivAt (fun t => fderiv ℝ ρ (x - t) v) (-(D2.flip v)) y := by
      intro v
      have h1 : HasFDerivAt (fun t => fderiv ℝ ρ (x - t)) (D2.comp (-ContinuousLinearMap.id ℝ Space)) y :=
        (hd.differentiable (by simp) (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
      have h2 := h1.clm_apply (hasFDerivAt_const v y)
      refine h2.congr_fderiv (ContinuousLinearMap.ext fun e => ?_)
      simp
    have hω : HasFDerivAt (fun t => fderiv ℝ ρ (x - t) u • w - fderiv ℝ ρ (x - t) w • u)
        ((-(D2.flip u)).smulRight w - (-(D2.flip w)).smulRight u) y :=
      ((hD u).smul_const w).sub ((hD w).smul_const u)
    have e1 : ∑ i, D2 (unitVector i) u * w i = D2 w u := by simpa using clm_sum_coord (D2.flip u) w
    have e2 : ∑ i, D2 (unitVector i) w * u i = D2 u w := by simpa using clm_sum_coord (D2.flip w) u
    rw [divergenceAt, hω.fderiv]
    simp
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, e1, e2, hsym w u]
    ring

theorem mollify_contDiff {Q : Space → Space} (hQ : LocallyIntegrable Q volume) {ρ : Space → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) : ContDiff ℝ ∞ (mollify Q ρ) :=
  hρc.contDiff_convolution_right smulFlip hQ hρ

theorem mollify_symm {Q : Space → Space} (hQ : LocallyIntegrable Q volume)
    (hann : ∀ φ : Space → Space, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ y, divergenceAt φ y = 0) →
      ∫ y, inner ℝ (Q y) (φ y) = 0)
    {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x u w : Space) :
    inner ℝ (fderiv ℝ (mollify Q ρ) x u) w = inner ℝ (fderiv ℝ (mollify Q ρ) x w) u := by
  have hdiff := hρc.hasFDerivAt_convolution_right smulFlip hQ (hρ.of_le (by norm_cast)) x
  have hdc : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by simp)
  have happ : ∀ v, fderiv ℝ (mollify Q ρ) x v = ∫ t, fderiv ℝ ρ (x - t) v • Q t := by
    intro v
    rw [mollify, hdiff.fderiv, convolution_precompR_apply smulFlip hQ (hρc.fderiv ℝ) hdc x v, convolution_def]
    rfl
  have hint : ∀ v, Integrable (fun t => fderiv ℝ ρ (x - t) v • Q t) := by
    intro v
    exact (hρc.fderiv_apply ℝ v).convolutionExists_right smulFlip hQ (hdc.clm_apply continuous_const) x
  have hin : ∀ v c, inner ℝ (fderiv ℝ (mollify Q ρ) x v) c
      = ∫ t, inner ℝ c (fderiv ℝ ρ (x - t) v • Q t) := by
    intro v c
    rw [happ, real_inner_comm, integral_inner (hint v)]
  obtain ⟨h1, h2, h3⟩ := stationary_pair hρ hρc x u w
  have hz := hann _ h1 h2 h3
  have iu : Integrable (fun t => inner ℝ w (fderiv ℝ ρ (x - t) u • Q t)) :=
    (innerSL ℝ w).integrable_comp (hint u)
  have iw : Integrable (fun t => inner ℝ u (fderiv ℝ ρ (x - t) w • Q t)) :=
    (innerSL ℝ u).integrable_comp (hint w)
  rw [hin, hin, ← sub_eq_zero, ← integral_sub iu iw, ← hz]
  congr 1
  funext t
  simp only [inner_sub_right, inner_smul_right]
  rw [real_inner_comm w, real_inner_comm u]

theorem approx_mollify {Q : Space → Space} (hQm : StronglyMeasurable Q) (hQ : LocallyIntegrable Q volume)
    (R : ℝ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ ρ : Space → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      ∫⁻ x in closedBall (0 : Space) R, ‖mollify Q ρ x - Q x‖ₑ ≤ ε := by
  set f := (closedBall (0 : Space) (R + 1)).indicator Q with hfdef
  have hf : Integrable f :=
    (hQ.integrableOn_isCompact (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall
  have hfm : StronglyMeasurable f := hQm.indicator measurableSet_closedBall
  have hε3 : ε / 3 ≠ 0 := by simp [hε]
  obtain ⟨g, hgc, hfg, hgcont, -⟩ := hf.exists_hasCompactSupport_lintegral_sub_le hε3
  set V := volume (closedBall (0 : Space) R)
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  obtain ⟨n, hn, hnV⟩ := ENNReal.exists_nnreal_pos_mul_lt hV hε3
  set θ : ℝ := (n : ℝ)
  have hθ : 0 < θ := by simpa [θ] using hn
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuous_iff.mp (hgc.uniformContinuous_of_continuous hgcont) θ hθ
  set r := min η 1
  have hr : 0 < r := lt_min hη one_pos
  let φ : ContDiffBump (0 : Space) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set ρ := φ.normed volume with hρdef
  refine ⟨ρ, φ.contDiff_normed, φ.hasCompactSupport_normed, ?_⟩
  have hρ0 : ∀ y, 0 ≤ ρ y := φ.nonneg_normed
  have hρsupp : ∀ y, ρ y ≠ 0 → ‖y‖ < r := fun y hy => by
    have : y ∈ Function.support ρ := hy
    rw [hρdef, φ.support_normed_eq] at this
    simpa using this
  have hρm : Measurable ρ := φ.continuous_normed.measurable
  have hρone : ∀ x : Space, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) = 1 := by
    intro x
    rw [lintegral_sub_left_eq_self (fun t => ENNReal.ofReal (ρ t)),
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed (Filter.Eventually.of_forall hρ0),
      φ.integral_normed, ENNReal.ofReal_one]
  have hρone' : ∀ t : Space, ∫⁻ x, ENNReal.ofReal (ρ (x - t)) = 1 := by
    intro t
    rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (ρ x)),
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed (Filter.Eventually.of_forall hρ0),
      φ.integral_normed, ENNReal.ofReal_one]
  have hpt : ∀ x ∈ closedBall (0 : Space) R, ‖mollify Q ρ x - Q x‖ₑ ≤
      (∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ) + ENNReal.ofReal θ + ‖g x - f x‖ₑ := by
    intro x hx
    have hxf : Q x = f x := by
      rw [hfdef, indicator_of_mem]
      exact closedBall_subset_closedBall (by linarith) hx
    have hconv : mollify Q ρ x = ∫ t, ρ (x - t) • f t := by
      rw [mollify, convolution_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      change ρ (x - t) • Q t = ρ (x - t) • f t
      by_cases h0 : ρ (x - t) = 0
      · simp [h0]
      · have ht := hρsupp _ h0
        rw [hfdef, indicator_of_mem]
        rw [mem_closedBall_zero_iff] at hx ⊢
        have := norm_sub_norm_le x t
        have h2 : ‖x - t‖ < 1 := lt_of_lt_of_le ht (min_le_right _ _)
        rw [norm_sub_rev] at h2
        have := norm_le_norm_add_norm_sub' t x
        linarith [norm_sub_rev t x]
    have hi1 : Integrable (fun t => ρ (x - t) • f t) := by
      have := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_right smulFlip hf.locallyIntegrable
        φ.continuous_normed x
      exact this
    have hi2 : Integrable (fun t => ρ (x - t) • f x) :=
      (φ.integrable_normed.comp_sub_left x).smul_const _
    have hone : ∫ t, ρ (x - t) = 1 := by
      rw [integral_sub_left_eq_self (fun t => ρ t), φ.integral_normed]
    have hdiff : mollify Q ρ x - Q x = ∫ t, ρ (x - t) • (f t - f x) := by
      rw [hconv, hxf]
      simp_rw [smul_sub]
      rw [integral_sub hi1 hi2, integral_smul_const, hone, one_smul]
    rw [hdiff]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ t, ‖ρ (x - t) • (f t - f x)‖ₑ
        ≤ ∫⁻ t, (ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ + ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal θ
            + ENNReal.ofReal (ρ (x - t)) * ‖g x - f x‖ₑ) := by
          refine lintegral_mono fun t => ?_
          rw [enorm_smul, Real.enorm_eq_ofReal (hρ0 _)]
          by_cases h0 : ρ (x - t) = 0
          · simp [h0]
          have hd : dist t x < η := by
            rw [dist_eq_norm, norm_sub_rev]
            exact lt_of_lt_of_le (hρsupp _ h0) (min_le_left _ _)
          have hgt : ‖g t - g x‖ₑ ≤ ENNReal.ofReal θ := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (by simpa [dist_eq_norm] using (hgη hd).le)
          calc ENNReal.ofReal (ρ (x - t)) * ‖f t - f x‖ₑ
              ≤ ENNReal.ofReal (ρ (x - t)) * (‖f t - g t‖ₑ + ‖g t - g x‖ₑ + ‖g x - f x‖ₑ) := by
                gcongr
                calc ‖f t - f x‖ₑ = ‖(f t - g t) + (g t - g x) + (g x - f x)‖ₑ := by congr 1; abel
                  _ ≤ ‖(f t - g t) + (g t - g x)‖ₑ + ‖g x - f x‖ₑ := enorm_add_le _ _
                  _ ≤ ‖f t - g t‖ₑ + ‖g t - g x‖ₑ + ‖g x - f x‖ₑ := by gcongr; exact enorm_add_le _ _
            _ ≤ ENNReal.ofReal (ρ (x - t)) * (‖f t - g t‖ₑ + ENNReal.ofReal θ + ‖g x - f x‖ₑ) := by gcongr
            _ = _ := by ring
      _ = (∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ) + ENNReal.ofReal θ + ‖g x - f x‖ₑ := by
          rw [lintegral_add_right _ (by fun_prop), lintegral_add_right _ (by fun_prop),
            lintegral_mul_const _ (by fun_prop), lintegral_mul_const _ (by fun_prop), hρone, one_mul, one_mul]
  have hfmeas : Measurable f := hfm.measurable
  have hgmeas : Measurable g := hgcont.measurable
  have hm2 : Measurable (fun p : Space × Space => ENNReal.ofReal (ρ (p.1 - p.2)) * ‖f p.2 - g p.2‖ₑ) := by
    fun_prop
  have hA : Measurable (fun x => ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ) := hm2.lintegral_prod_right'
  have hθn : ENNReal.ofReal θ = (n : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  calc ∫⁻ x in closedBall (0 : Space) R, ‖mollify Q ρ x - Q x‖ₑ
      ≤ ∫⁻ x in closedBall (0 : Space) R,
          ((∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ) + ENNReal.ofReal θ + ‖g x - f x‖ₑ) :=
        setLIntegral_mono' measurableSet_closedBall hpt
    _ = (∫⁻ x in closedBall (0 : Space) R, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ)
          + ENNReal.ofReal θ * V + ∫⁻ x in closedBall (0 : Space) R, ‖g x - f x‖ₑ := by
        rw [lintegral_add_right _ (by fun_prop), lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · calc (∫⁻ x in closedBall (0 : Space) R, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ)
              ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ := setLIntegral_le_lintegral _ _
            _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ (x - t)) * ‖f t - g t‖ₑ :=
                lintegral_lintegral_swap hm2.aemeasurable
            _ = ∫⁻ t, ‖f t - g t‖ₑ := by
                congr 1
                funext t
                rw [lintegral_mul_const _ (by fun_prop), hρone', one_mul]
            _ ≤ ε / 3 := hfg
        · rw [hθn]
          exact hnV.le
        · calc ∫⁻ x in closedBall (0 : Space) R, ‖g x - f x‖ₑ ≤ ∫⁻ x, ‖g x - f x‖ₑ := setLIntegral_le_lintegral _ _
            _ = ∫⁻ x, ‖f x - g x‖ₑ := by simp_rw [enorm_sub_rev]
            _ ≤ ε / 3 := hfg
    _ = ε := ENNReal.add_thirds ε

end Breakdown.CertCell.AnnihilatorGradient.Internal
