import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

private theorem sq_add_le_two_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  have e : ((2 : ℝ) - 1) = 1 := by norm_num
  rw [e, ENNReal.rpow_one] at h
  simpa only [ENNReal.rpow_two] using h

private theorem symX_add_ae (a b : X) : symX (a + b) =ᵐ[volume] symX a + symX b :=
  Lp.coeFn_add (a : L2C) (b : L2C)

private theorem homSob_add_le (k : ℕ) (a b : X) :
    homSob k (a + b) ≤ 2 * (homSob k a + homSob k b) := by
  have hma : AEMeasurable (fun ξ => ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symX a ξ‖ₑ ^ 2) volume := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable.mul ?_
    exact (Lp.aestronglyMeasurable (a : L2C)).enorm.pow_const 2
  calc homSob k (a + b)
      = ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symX a ξ + symX b ξ‖ₑ ^ 2 := by
        unfold homSob homNormSq
        refine lintegral_congr_ae ?_
        filter_upwards [symX_add_ae a b] with ξ h
        rw [h, Pi.add_apply]
    _ ≤ ∫⁻ ξ, 2 * (ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symX a ξ‖ₑ ^ 2 +
          ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symX b ξ‖ₑ ^ 2) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symX a ξ + symX b ξ‖ₑ ^ 2
            ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * (2 * (‖symX a ξ‖ₑ ^ 2 + ‖symX b ξ‖ₑ ^ 2)) :=
              mul_le_mul' le_rfl ((pow_le_pow_left₀ (by positivity) (enorm_add_le _ _) 2).trans
                (sq_add_le_two_mul _ _))
          _ = _ := by ring
    _ = 2 * (homSob k a + homSob k b) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hma]
        rfl

private theorem dilX_mul_inv_apply {μ : ℝ} (hμ : 0 < μ) (v : X) : dilX μ (dilX μ⁻¹ v) = v := by
  have h := dilation_holds.2.2.1 μ μ⁻¹ hμ (inv_pos.mpr hμ)
  rw [mul_inv_cancel₀ hμ.ne', dilation_holds.2.1] at h
  simpa using (congrArg (fun T : X →L[ℝ] X => T v) h).symm

private def windowCurve (w : ℝ → X) (s₀ t : ℝ) : X := dilX (1 - t)⁻¹ (w (s₀ - Real.log (1 - t)))

private theorem eq_dilX_windowCurve (w : ℝ → X) (s₀ σ : ℝ) :
    w σ = dilX (exp (-(σ - s₀))) (windowCurve w s₀ (1 - exp (-(σ - s₀)))) := by
  unfold windowCurve
  rw [sub_sub_cancel, Real.log_exp, show s₀ - -(σ - s₀) = σ by ring,
    dilX_mul_inv_apply (exp_pos _)]

set_option maxHeartbeats 1000000 in
private theorem homSobolev_near (hOW : OrbitWindows) (hMS : MildSmoothing) (hDS : DilateSymbol)
    {w : ℝ → X} {P : ℝ} {R : Space ≃ₗᵢ[ℝ] Space}
    (hw : realization.F.IsOrbit (realization.rot R) w P) (k : ℕ) (s₀ s : ℝ) (hs : s₀ < s) :
    homSob k (w s) < ⊤ ∧ Tendsto (fun σ => homSob k (w σ - w s)) (𝓝 s) (𝓝 0) := by
  obtain ⟨c, hc⟩ : ∃ c, exp (-(s - s₀)) = c := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [← hc]
    exact exp_pos _
  have hc1 : c < 1 := by
    rw [← hc, Real.exp_lt_one_iff]
    linarith
  have hT0 : 0 < 1 - c / 2 := by linarith
  have hT1 : 1 - c / 2 < 1 := by linarith
  have ha : (1 - c) / 2 ∈ Ioo 0 (1 - c / 2) := ⟨by linarith, by linarith⟩
  have hmild : IsMildX (windowCurve w s₀) 0 (1 - c / 2) := hOW w P R hw s₀ _ hT0 hT1
  have hS : IsHomSobolevCurve k (windowCurve w s₀) (Icc ((1 - c) / 2) (1 - c / 2)) :=
    hMS _ 0 _ hT0 hmild _ ha k
  have htI : 1 - c ∈ Ioo ((1 - c) / 2) (1 - c / 2) := ⟨by linarith, by linarith⟩
  have hfin : homSob k (windowCurve w s₀ (1 - c)) < ⊤ := hS.1 _ (Ioo_subset_Icc_self htI)
  have hws : w s = dilX c (windowCurve w s₀ (1 - c)) := by
    rw [← hc]
    exact eq_dilX_windowCurve w s₀ s
  refine ⟨?_, ?_⟩
  · rw [hws, (hDS c hc0 _).1 k]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hμt : Tendsto (fun σ => exp (-(σ - s₀))) (𝓝 s) (𝓝 c) := by
    rw [← hc]
    exact (continuous_exp.comp (by fun_prop : Continuous fun σ : ℝ => -(σ - s₀))).tendsto s
  have htn : Tendsto (fun σ => 1 - exp (-(σ - s₀))) (𝓝 s) (𝓝 (1 - c)) :=
    tendsto_const_nhds.sub hμt
  have htt : Tendsto (fun σ => 1 - exp (-(σ - s₀))) (𝓝 s)
      (𝓝[Icc ((1 - c) / 2) (1 - c / 2)] (1 - c)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htn ?_
    exact (htn.eventually (isOpen_Ioo.mem_nhds htI)).mono fun σ h => Ioo_subset_Icc_self h
  have h1 : Tendsto (fun σ => homSob k (windowCurve w s₀ (1 - exp (-(σ - s₀))) -
      windowCurve w s₀ (1 - c))) (𝓝 s) (𝓝 0) :=
    (hS.2 (1 - c) (Ioo_subset_Icc_self htI)).comp htt
  have hfac : Tendsto (fun σ => ENNReal.ofReal (exp (-(σ - s₀)) ^ ((k : ℝ) + 1 / 2))) (𝓝 s)
      (𝓝 (ENNReal.ofReal (c ^ ((k : ℝ) + 1 / 2)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hμt.rpow_const (Or.inl hc0.ne'))
  have h2 : Tendsto (fun ν => homSob k (dilX ν (windowCurve w s₀ (1 - c)) -
      dilX c (windowCurve w s₀ (1 - c)))) (𝓝 c) (𝓝 0) :=
    ((hDS c hc0 _).2.1 k).resolve_right hfin.ne
  have hlim := ENNReal.Tendsto.const_mul
    ((ENNReal.Tendsto.mul hfac (Or.inr ENNReal.zero_ne_top) h1
      (Or.inr ENNReal.ofReal_ne_top)).add (h2.comp hμt)) (a := 2) (Or.inr (by norm_num))
  have e : (2 : ℝ≥0∞) * (ENNReal.ofReal (c ^ ((k : ℝ) + 1 / 2)) * 0 + 0) = 0 := by simp
  rw [e] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => by positivity) fun σ => ?_
  have hsplit : w σ - w s = dilX (exp (-(σ - s₀)))
      (windowCurve w s₀ (1 - exp (-(σ - s₀))) - windowCurve w s₀ (1 - c)) +
      (dilX (exp (-(σ - s₀))) (windowCurve w s₀ (1 - c)) - dilX c (windowCurve w s₀ (1 - c))) := by
    rw [map_sub, sub_add_sub_cancel, ← hws, ← eq_dilX_windowCurve w s₀ σ]
  rw [hsplit]
  refine (homSob_add_le k _ _).trans ?_
  rw [(hDS _ (exp_pos _) _).1 k]
  exact le_rfl

theorem orbitHomSobolevOfWindows_holds : OrbitHomSobolevOfWindows := by
  intro hOW hMS hDS w P R hw k
  refine ⟨fun s _ => (homSobolev_near hOW hMS hDS hw k (s - 1) s (by linarith)).1, fun s _ => ?_⟩
  rw [nhdsWithin_univ]
  exact (homSobolev_near hOW hMS hDS hw k (s - 1) s (by linarith)).2

end Breakdown.FarField
