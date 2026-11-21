import Breakdown.Frac.ScaledStatements
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown

namespace ScaledMildFramework

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {κ : ℝ}

theorem D_inv_apply (F : ScaledMildFramework X κ) (μ : ℝ) (hμ : 0 < μ) (x : X) :
    F.D μ⁻¹ (F.D μ x) = x := by
  rw [← ContinuousLinearMap.comp_apply (F.D μ⁻¹) (F.D μ), ← F.D_mul _ _ (inv_pos.mpr hμ) hμ,
    inv_mul_cancel₀ hμ.ne', F.D_one, ContinuousLinearMap.id_apply]

theorem selfSimilar_continuousOn (F : ScaledMildFramework X κ) (w : ℝ → X) (hw : Continuous w)
    (s₀ : ℝ) : ContinuousOn (F.selfSimilar w s₀) (Ico 0 1) := by
  intro t₀ ht₀
  have hpos : 0 < 1 - t₀ := by linarith [ht₀.2]
  have ha : ContinuousWithinAt (fun t : ℝ => (1 - t)⁻¹) (Ico 0 1) t₀ :=
    ((continuous_const.sub continuous_id).continuousAt.inv₀ hpos.ne').continuousWithinAt
  have hb : ContinuousAt (fun t : ℝ => w (s₀ - Real.log (1 - t))) t₀ :=
    hw.continuousAt.comp
      (continuousAt_const.sub ((continuous_const.sub continuous_id).continuousAt.log hpos.ne'))
  have hmem : ∀ t ∈ Ico (0 : ℝ) 1, (1 - t)⁻¹ ∈ Ioi (0 : ℝ) := fun t ht => by
    have h := ht.2
    show 0 < (1 - t)⁻¹
    exact inv_pos.mpr (by linarith)
  have h1 : Tendsto (fun t : ℝ => F.D (1 - t)⁻¹ (w (s₀ - Real.log (1 - t₀))))
      (𝓝[Ico 0 1] t₀) (𝓝 (F.D (1 - t₀)⁻¹ (w (s₀ - Real.log (1 - t₀))))) :=
    ((F.D_cont (w (s₀ - Real.log (1 - t₀)))) _ (inv_pos.mpr hpos)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ha.tendsto, eventually_nhdsWithin_of_forall hmem⟩)
  have h2 : Tendsto (fun t : ℝ => F.D (1 - t)⁻¹
      (w (s₀ - Real.log (1 - t)) - w (s₀ - Real.log (1 - t₀)))) (𝓝[Ico 0 1] t₀) (𝓝 0) := by
    have hn : ∀ᶠ t in 𝓝[Ico 0 1] t₀, ‖F.D (1 - t)⁻¹
        (w (s₀ - Real.log (1 - t)) - w (s₀ - Real.log (1 - t₀)))‖ =
        ((1 - t)⁻¹) ^ κ *
          ‖w (s₀ - Real.log (1 - t)) - w (s₀ - Real.log (1 - t₀))‖ :=
      eventually_nhdsWithin_of_forall (fun t ht => F.D_norm _ (hmem t ht) _)
    have hlim : Tendsto (fun t : ℝ => ((1 - t)⁻¹) ^ κ *
        ‖w (s₀ - Real.log (1 - t)) - w (s₀ - Real.log (1 - t₀))‖) (𝓝[Ico 0 1] t₀)
        (𝓝 (((1 - t₀)⁻¹) ^ κ *
          ‖w (s₀ - Real.log (1 - t₀)) - w (s₀ - Real.log (1 - t₀))‖)) :=
      (ha.tendsto.rpow_const (Or.inl (inv_pos.mpr hpos).ne')).mul
        ((hb.tendsto.mono_left nhdsWithin_le_nhds).sub_const _).norm
    rw [sub_self, norm_zero, mul_zero] at hlim
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (hlim.congr' (hn.mono fun t h => h.symm))
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3.congr (fun t => by
    rw [← map_add, add_sub_cancel]
    rfl)

theorem selfSimilar_eq (F : ScaledMildFramework X κ) (w : ℝ → X)
    (hflow : ∀ s' s, s' ≤ s →
      IntervalIntegrable (fun σ => F.Ks (s - σ) (w σ) (w σ)) volume s' s ∧
        w s = F.S (s - s') (w s') + ∫ σ in s'..s, F.Ks (s - σ) (w σ) (w σ))
    (s₀ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    F.selfSimilar w s₀ t = F.G (t - 0) (F.selfSimilar w s₀ 0) +
      ∫ r in (0 : ℝ)..t, F.K (t - r) (F.selfSimilar w s₀ r) (F.selfSimilar w s₀ r) := by
  have hpos : 0 < 1 - t := by linarith
  have hL : Real.exp (Real.log (1 - t)) = 1 - t := Real.exp_log hpos
  have hLle : Real.log (1 - t) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  obtain ⟨hI, hws⟩ := hflow s₀ (s₀ - Real.log (1 - t)) (by linarith)
  have hS : F.S (s₀ - Real.log (1 - t) - s₀) = (F.D (1 - t)).comp (F.G t) := by
    unfold ScaledMildFramework.S
    rw [show -(s₀ - Real.log (1 - t) - s₀) = Real.log (1 - t) by ring, hL,
      show 1 - (1 - t) = t by ring]
  have h0 : F.selfSimilar w s₀ 0 = w s₀ := by
    simp only [ScaledMildFramework.selfSimilar, sub_zero, inv_one, Real.log_one, F.D_one,
      ContinuousLinearMap.id_apply]
  have hu : F.selfSimilar w s₀ t = F.D (1 - t)⁻¹ (w (s₀ - Real.log (1 - t))) := rfl
  rw [h0, sub_zero, hu, hws, hS, map_add, ContinuousLinearMap.comp_apply, D_inv_apply F _ hpos,
    add_right_inj, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
    intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le ht0,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have himg : (fun σ => 1 - Real.exp (-(σ - s₀))) '' Ioo s₀ (s₀ - Real.log (1 - t)) =
      Ioo 0 t := by
    ext r
    constructor
    · rintro ⟨σ, ⟨h1, h2⟩, rfl⟩
      constructor
      · have := Real.exp_lt_exp.mpr (show -(σ - s₀) < 0 by linarith)
        rw [Real.exp_zero] at this
        linarith
      · have := Real.exp_lt_exp.mpr (show Real.log (1 - t) < -(σ - s₀) by linarith)
        rw [hL] at this
        linarith
    · rintro ⟨h1, h2⟩
      have hr : 0 < 1 - r := by linarith
      refine ⟨s₀ - Real.log (1 - r), ⟨?_, ?_⟩, ?_⟩
      · have := Real.log_neg hr (by linarith)
        linarith
      · have := Real.log_lt_log hpos (show 1 - t < 1 - r by linarith)
        linarith
      · show 1 - Real.exp (-(s₀ - Real.log (1 - r) - s₀)) = r
        rw [show -(s₀ - Real.log (1 - r) - s₀) = Real.log (1 - r) by ring, Real.exp_log hr]
        ring
  have hder : ∀ σ ∈ Ioo s₀ (s₀ - Real.log (1 - t)),
      HasDerivWithinAt (fun σ => 1 - Real.exp (-(σ - s₀))) (Real.exp (-(σ - s₀)))
        (Ioo s₀ (s₀ - Real.log (1 - t))) σ := by
    intro σ _
    have := ((((hasDerivAt_id' σ).sub_const s₀).neg).exp).const_sub 1
    exact this.hasDerivWithinAt.congr_deriv (by simp)
  have hinj : InjOn (fun σ => 1 - Real.exp (-(σ - s₀))) (Ioo s₀ (s₀ - Real.log (1 - t))) := by
    intro a _ b _ hab
    have h := Real.exp_injective (show Real.exp (-(a - s₀)) = Real.exp (-(b - s₀)) by
      simp only at hab
      linarith)
    linarith
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (fun r => F.K (t - r) (F.selfSimilar w s₀ r) (F.selfSimilar w s₀ r))
  rw [himg] at hcv
  rw [hcv]
  refine setIntegral_congr_fun measurableSet_Ioo (fun σ hσ => ?_)
  have hE : 0 < Real.exp (-(σ - s₀)) := Real.exp_pos _
  have hμ : 0 < Real.exp (σ - s₀) := Real.exp_pos _
  have hEμ : Real.exp (-(σ - s₀)) = (Real.exp (σ - s₀))⁻¹ := Real.exp_neg _
  have hsim : F.selfSimilar w s₀ (1 - Real.exp (-(σ - s₀))) = F.D (Real.exp (σ - s₀)) (w σ) := by
    unfold ScaledMildFramework.selfSimilar
    rw [show 1 - (1 - Real.exp (-(σ - s₀))) = Real.exp (-(σ - s₀)) by ring, Real.log_exp, hEμ,
      inv_inv, show s₀ - -(σ - s₀) = σ by ring]
  have hτeq : t - (1 - Real.exp (-(σ - s₀))) = Real.exp (-(σ - s₀)) - Real.exp (Real.log (1 - t)) := by
    rw [hL]
    ring
  have hτpos : 0 < Real.exp (-(σ - s₀)) - Real.exp (Real.log (1 - t)) := by
    have := Real.exp_lt_exp.mpr (show Real.log (1 - t) < -(σ - s₀) by linarith [hσ.2])
    linarith
  have hmul : Real.exp (σ - s₀) * (Real.exp (-(σ - s₀)) - Real.exp (Real.log (1 - t))) =
      1 - Real.exp (-(s₀ - Real.log (1 - t) - σ)) := by
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add, show σ - s₀ + -(σ - s₀) = 0 by ring,
      Real.exp_zero, show σ - s₀ + Real.log (1 - t) = -(s₀ - Real.log (1 - t) - σ) by ring]
  have hprod : (1 - t)⁻¹ * Real.exp (-(s₀ - Real.log (1 - t) - σ)) = Real.exp (σ - s₀) := by
    have hi : (1 - t)⁻¹ = Real.exp (-Real.log (1 - t)) := by rw [Real.exp_neg, hL]
    rw [hi, ← Real.exp_add]
    congr 1
    ring
  have hDK := F.D_K _ _ hμ hτpos (w σ) (w σ)
  unfold ScaledMildFramework.Ks
  rw [← ContinuousLinearMap.comp_apply (F.D (1 - t)⁻¹) (F.D _),
    ← F.D_mul _ _ (inv_pos.mpr hpos) (Real.exp_pos _), hprod, ← hmul, hτeq, hsim,
    abs_of_pos hE, ← hDK, smul_smul, ← Real.exp_add, show -(σ - s₀) + (σ - s₀) = 0 by ring,
    Real.exp_zero, one_smul]

end ScaledMildFramework

theorem scaledOrbitPhysical_of (h1 : VarConstIntegralStatement) : ScaledOrbitPhysicalStatement := by
  intro X _ _ _ κ _ F w hw hflow s₀
  have hc := ScaledMildFramework.selfSimilar_continuousOn F w hw s₀
  refine ⟨hc, fun t ht => ⟨?_, ScaledMildFramework.selfSimilar_eq F w hflow s₀ t ht.1 ht.2⟩⟩
  have hc' : ContinuousOn (F.selfSimilar w s₀) (Icc 0 t) := hc.mono (Icc_subset_Ico_right ht.2)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'
  exact (h1 X F.toHeatBilinear (F.selfSimilar w s₀) (F.selfSimilar w s₀) 0 t M M ht.1 hc' hc'
    hM hM).1 t ⟨ht.1, le_rfl⟩

end Breakdown
