import Breakdown.CertCell.SixthPowerWeakCutoff

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ContDiff ENNReal

noncomputable section

namespace Breakdown

private lemma continuous_matSq : Continuous matSq := by
  unfold matSq
  fun_prop

private lemma matSq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma sq_norm_integral_le {ρ : Space → ℝ} (hρ : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ)
    (hρ1 : ∫ t, ρ t = 1) {v : Space → Space} (hv : Integrable (fun t => ρ t • v t))
    (hv2 : Integrable (fun t => ρ t * ‖v t‖ ^ 2)) :
    ‖∫ t, ρ t • v t‖ ^ 2 ≤ ∫ t, ρ t * ‖v t‖ ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A, ∫ t, ρ t • v t = A := ⟨_, rfl⟩
  rw [hA]
  have hpt : ∀ t, 2 * inner ℝ A (ρ t • v t) - ρ t * ‖A‖ ^ 2 ≤ ρ t * ‖v t‖ ^ 2 := by
    intro t
    have h0 : 0 ≤ ρ t * ‖v t - A‖ ^ 2 := mul_nonneg (hρ t) (sq_nonneg _)
    rw [norm_sub_sq_real] at h0
    rw [inner_smul_right, real_inner_comm]
    nlinarith
  have hi1 : Integrable (fun t => 2 * inner ℝ A (ρ t • v t)) := (hv.const_inner A).const_mul 2
  have hi : Integrable (fun t => 2 * inner ℝ A (ρ t • v t) - ρ t * ‖A‖ ^ 2) :=
    hi1.sub (hρi.mul_const _)
  calc ‖A‖ ^ 2 = ∫ t, (2 * inner ℝ A (ρ t • v t) - ρ t * ‖A‖ ^ 2) := by
        rw [integral_sub hi1 (hρi.mul_const _), integral_const_mul, integral_inner hv, hA,
          integral_mul_const, hρ1, real_inner_self_eq_norm_sq]
        ring
    _ ≤ ∫ t, ρ t * ‖v t‖ ^ 2 := integral_mono hi hv2 hpt

private lemma sixth_le_tangent {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    a ^ 6 + 6 * a ^ 5 * (r - a) ≤ r ^ 6 := by
  have h1 : r ^ 6 - (a ^ 6 + 6 * a ^ 5 * (r - a)) =
      (r - a) ^ 2 * (r ^ 4 + 2 * r ^ 3 * a + 3 * r ^ 2 * a ^ 2 + 4 * r * a ^ 3 + 5 * a ^ 4) := by
    ring
  have h2 : 0 ≤ (r - a) ^ 2 *
      (r ^ 4 + 2 * r ^ 3 * a + 3 * r ^ 2 * a ^ 2 + 4 * r * a ^ 3 + 5 * a ^ 4) := by
    positivity
  linarith

private lemma sixth_norm_integral_le {ρ : Space → ℝ} (hρ : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ)
    (hρ1 : ∫ t, ρ t = 1) {v : Space → Space} (hv : Integrable (fun t => ρ t • v t))
    (hv6 : Integrable (fun t => ρ t * ‖v t‖ ^ 6)) :
    ‖∫ t, ρ t • v t‖ ^ 6 ≤ ∫ t, ρ t * ‖v t‖ ^ 6 := by
  have hnorm : ∀ t, ‖ρ t • v t‖ = ρ t * ‖v t‖ := fun t => by
    rw [norm_smul, Real.norm_of_nonneg (hρ t)]
  have hn : Integrable (fun t => ρ t * ‖v t‖) := hv.norm.congr (Eventually.of_forall hnorm)
  obtain ⟨a, ha_def⟩ : ∃ a, ∫ t, ρ t * ‖v t‖ = a := ⟨_, rfl⟩
  have ha : 0 ≤ a := ha_def ▸ integral_nonneg fun t => mul_nonneg (hρ t) (norm_nonneg _)
  have hA : ‖∫ t, ρ t • v t‖ ≤ a := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp_rw [hnorm]
    exact ha_def
  have hpt : ∀ t, a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖) - 6 * a ^ 6 * ρ t ≤
      ρ t * ‖v t‖ ^ 6 := by
    intro t
    have := mul_le_mul_of_nonneg_left (sixth_le_tangent (norm_nonneg (v t)) ha) (hρ t)
    nlinarith
  have hi1 : Integrable (fun t => a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖)) :=
    (hρi.const_mul _).add (hn.const_mul _)
  have hi : Integrable (fun t => a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖) - 6 * a ^ 6 * ρ t) :=
    hi1.sub (hρi.const_mul _)
  have hint : ∫ t, (a ^ 6 * ρ t + 6 * a ^ 5 * (ρ t * ‖v t‖) - 6 * a ^ 6 * ρ t) = a ^ 6 := by
    rw [integral_sub hi1 (hρi.const_mul _), integral_add (hρi.const_mul _) (hn.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, hρ1, ha_def]
    ring
  calc ‖∫ t, ρ t • v t‖ ^ 6 ≤ a ^ 6 := pow_le_pow_left₀ (norm_nonneg _) hA 6
    _ = _ := hint.symm
    _ ≤ _ := integral_mono hi hv6 hpt

private lemma fderiv_convolution_column (φ : ContDiffBump (0 : Space)) {w : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient w G) (x : Space) (i : Fin 3) :
    fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) x (unitVector i) =
      ∫ t, φ.normed volume t • G (x - t) (unitVector i) := by
  have hc1 : ContDiff ℝ 1 (φ.normed volume) := φ.contDiff_normed
  have hd := φ.hasCompactSupport_normed.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hc1 hw.1 x
  have hex : ConvolutionExistsAt (fderiv ℝ (φ.normed volume)) w x
      (precompL Space (lsmul ℝ ℝ)) volume :=
    (φ.hasCompactSupport_normed.fderiv ℝ).convolutionExists_left _
      (hc1.continuous_fderiv one_ne_zero) hw.1 x
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp only [precompL_apply, lsmul_apply]
  have hψ : IsTestFunction (fun y => φ.normed volume (x - y)) :=
    ⟨φ.contDiff_normed.comp (contDiff_const.sub contDiff_id),
      φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hweak := hw.2.2 _ hψ i
  have hder : ∀ y, fderiv ℝ (fun y => φ.normed volume (x - y)) y (unitVector i) =
      -fderiv ℝ (φ.normed volume) (x - y) (unitVector i) := by
    intro y
    have h1 : HasFDerivAt (fun y => φ.normed volume (x - y))
        ((fderiv ℝ (φ.normed volume) (x - y)).comp (-ContinuousLinearMap.id ℝ Space)) y :=
      ((hc1.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).const_sub x)
    rw [h1.fderiv]
    simp
  simp_rw [hder, neg_smul, integral_neg, neg_neg] at hweak
  have e1 : ∫ t, φ.normed volume t • G (x - t) (unitVector i) =
      ∫ y, φ.normed volume (x - y) • G y (unitVector i) := by
    rw [← integral_sub_left_eq_self (fun y => φ.normed volume (x - y) • G y (unitVector i))
      volume x]
    simp only [sub_sub_cancel]
  have e2 : ∫ t, (fderiv ℝ (φ.normed volume) t (unitVector i)) • w (x - t) =
      ∫ y, (fderiv ℝ (φ.normed volume) (x - y) (unitVector i)) • w y := by
    rw [← integral_sub_left_eq_self
      (fun y => (fderiv ℝ (φ.normed volume) (x - y) (unitVector i)) • w y) volume x]
    simp only [sub_sub_cancel]
  rw [e1, e2, hweak]

private lemma mollified_sixthPower_bound {C : ℝ} (hC : 0 ≤ C) (h : SmoothSixthPowerBound C)
    (φ : ContDiffBump (0 : Space)) {w : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient w G) (h6 : Integrable (fun y => ‖w y‖ ^ 6))
    (h2 : Integrable (fun y => matSq (G y))) :
    Integrable (fun y => ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 6) ∧
      ∫ y, ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 6 ≤ (C * ∫ y, matSq (G y)) ^ 3 := by
  have hρ0 : ∀ t, 0 ≤ φ.normed volume t := φ.nonneg_normed
  have hρc : Continuous (φ.normed volume) := (φ.contDiff_normed (n := 0)).continuous
  have hρs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hρi : Integrable (φ.normed volume) := hρc.integrable_of_hasCompactSupport hρs
  have hρ1 : ∫ t, φ.normed volume t = 1 := φ.integral_normed
  have hWc : ContDiff ℝ 1 (φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) :=
    hρs.contDiff_convolution_left _ φ.contDiff_normed hw.1
  have hpt6 : ∀ x, ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) x‖ ^ 6 ≤
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun y => ‖w y‖ ^ 6)) x := by
    intro x
    have ha : ConvolutionExistsAt (φ.normed volume) w x (lsmul ℝ ℝ) volume :=
      hρs.convolutionExists_left _ hρc hw.1 x
    have hb : ConvolutionExistsAt (φ.normed volume) (fun y => ‖w y‖ ^ 6) x (lsmul ℝ ℝ) volume :=
      hρs.convolutionExists_left _ hρc h6.locallyIntegrable x
    simp only [convolution_def, lsmul_apply, smul_eq_mul]
    exact sixth_norm_integral_le hρ0 hρi hρ1 ha (by simpa [ConvolutionExistsAt] using hb)
  have hI6 : Integrable (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun y => ‖w y‖ ^ 6)) :=
    hρi.integrable_convolution _ h6
  have hW6 : Integrable (fun y => ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 6) :=
    hI6.mono' (hWc.continuous.norm.pow 6).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hpt6 x)
  have hptG : ∀ x, matSq (fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) x) ≤
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun y => matSq (G y))) x := by
    intro x
    have hGm : AEStronglyMeasurable (fun t => G (x - t)) volume :=
      hw.2.1.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    have hF : ConvolutionExistsAt (φ.normed volume) (fun y => matSq (G y)) x (lsmul ℝ ℝ)
        volume := hρs.convolutionExists_left _ hρc h2.locallyIntegrable x
    have hF' : Integrable (fun t => φ.normed volume t * matSq (G (x - t))) := by
      simpa [ConvolutionExistsAt] using hF
    have hM : ConvolutionExistsAt (φ.normed volume) G x (lsmul ℝ ℝ) volume :=
      hρs.convolutionExists_left _ hρc hw.2.1 x
    have hv : ∀ i : Fin 3, Integrable (fun t => φ.normed volume t • G (x - t) (unitVector i)) := by
      intro i
      simpa using (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrable_comp hM
    have hv2 : ∀ i : Fin 3,
        Integrable (fun t => φ.normed volume t * ‖G (x - t) (unitVector i)‖ ^ 2) := by
      intro i
      refine hF'.mono' (hρc.aestronglyMeasurable.mul
        ((((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
          hGm).norm).pow 2)) (Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (sq_nonneg _))]
      refine mul_le_mul_of_nonneg_left ?_ (hρ0 t)
      unfold matSq
      exact Finset.single_le_sum (f := fun j => ‖G (x - t) (unitVector j)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    simp only [convolution_def, lsmul_apply, smul_eq_mul]
    unfold matSq
    simp_rw [fderiv_convolution_column φ hw x, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => hv2 i)]
    exact Finset.sum_le_sum fun i _ => sq_norm_integral_le hρ0 hρi hρ1 (hv i) (hv2 i)
  have hIG : Integrable (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun y => matSq (G y))) :=
    hρi.integrable_convolution _ h2
  have hDW : Integrable (fun y => matSq (fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) y)) :=
    hIG.mono' ((continuous_matSq.comp (hWc.continuous_fderiv one_ne_zero)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (matSq_nonneg _)]
        exact hptG x)
  have hY : ∫ y, matSq (fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] w) y) ≤
      ∫ y, matSq (G y) := by
    refine (integral_mono hDW hIG hptG).trans (le_of_eq ?_)
    rw [integral_convolution _ hρi h2, hρ1]
    simp
  refine ⟨hW6, (sixthPower_le_of_contDiff_integrable hC h _ hWc hW6 hDW).trans ?_⟩
  exact pow_le_pow_left₀ (mul_nonneg hC (integral_nonneg fun _ => matSq_nonneg _))
    (mul_le_mul_of_nonneg_left hY hC) 3

private def shrinkingBump (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := 1 / ((n : ℝ) + 2)
  rOut := 2 / ((n : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by gcongr; norm_num

theorem sixthPowerGradientBound_of {C : ℝ} (hC : 0 ≤ C) (h : SmoothSixthPowerBound C) :
    SixthPowerGradientBound C := by
  intro w G hw h6 h2
  have hw6 : Integrable (fun y => ‖w y‖ ^ 6) :=
    ⟨hw.1.aestronglyMeasurable.norm.pow 6,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by positivity)).2 h6⟩
  have hG2 : Integrable (fun y => matSq (G y)) :=
    ⟨continuous_matSq.comp_aestronglyMeasurable hw.2.1.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => matSq_nonneg _)).2 h2⟩
  have hCY : 0 ≤ C * ∫ y, matSq (G y) := mul_nonneg hC (integral_nonneg fun _ => matSq_nonneg _)
  have hK0 : 0 ≤ (C * ∫ y, matSq (G y)) ^ 3 := pow_nonneg hCY 3
  have hbound := fun n => mollified_sixthPower_bound hC h (shrinkingBump n) hw hw6 hG2
  have hrad : Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) := by
    simp only [shrinkingBump]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (K := 2)
    hrad (Eventually.of_forall fun n => by simp only [shrinkingBump]; rw [mul_one_div]) hw.1
  have hlim : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) ≤
      ENNReal.ofReal ((C * ∫ y, matSq (G y)) ^ 3) := by
    calc ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)
        = ∫⁻ y, liminf (fun n => ENNReal.ofReal
            (‖((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 6)) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with y hy
          exact (((ENNReal.continuous_ofReal.tendsto _).comp
            ((hy.norm).pow 6))).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal
            (‖((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 6)) atTop :=
          lintegral_liminf_le' fun n => (hbound n).1.aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal ((C * ∫ y, matSq (G y)) ^ 3) := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hbound n).1
            (Eventually.of_forall fun y => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hbound n).2
  have hX : ∫ y, ‖w y‖ ^ 6 ≤ (C * ∫ y, matSq (G y)) ^ 3 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => by positivity)
      hw6.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 hlim
  calc (∫ y, ‖w y‖ ^ 6) ^ ((1 : ℝ) / 3) ≤ ((C * ∫ y, matSq (G y)) ^ 3) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) hX (by norm_num)
    _ = C * ∫ y, matSq (G y) := by
        rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast hCY (by norm_num)

end Breakdown
