import Breakdown.Cert.CoerciveTestDensityProof
import Breakdown.Cert.CoerciveTestDensityCurlApprox

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.CurlGraphDensity

open Internal.TestDensityProof

theorem exists_solenoidalPart_approx (F : ℝ → Space → Space)
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (hp : IsTimePeriodic F)
    (hR : ∃ R, ∀ σ y, R < ‖y‖ → F σ y = 0) :
    ∃ Q' : ℝ → Space → Space, IsSolenoidalPartOf F Q' ∧
      ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
        Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q' σ y‖ ^ 2)) atTop (nhds 0) ∧
        Tendsto (fun n => periodLIntegral (fun σ y =>
            ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) atTop (nhds 0) :=
  Breakdown.Coercive.exists_solenoidalPart_approx_core F hF hp hR

theorem periodLIntegral_congr {f g : ℝ → Space → ℝ}
    (h : ∀ᵐ z : ℝ × Space, f z.1 z.2 = g z.1 z.2) : periodLIntegral f = periodLIntegral g := by
  have h1 : ∀ᵐ z ∂periodMeasure, f z.1 z.2 = g z.1 z.2 := by
    rw [periodMeasure_eq]
    exact ae_restrict_of_ae h
  have h2 := Measure.ae_ae_of_ae_prod h1
  unfold periodLIntegral
  refine lintegral_congr_ae ?_
  filter_upwards [h2] with σ hσ
  refine lintegral_congr_ae ?_
  filter_upwards [hσ] with y hy
  rw [hy]

theorem lt_top_of_memLp {X : ℝ → Space → Space}
    (h : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ := by
  have hi := (memLp_two_iff_integrable_sq_norm h.1).1 h
  unfold periodLIntegral
  rw [← lintegral_prod _ hi.1.aemeasurable.ennreal_ofReal]
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).1 hi.2

theorem memLp_of_continuous {Y : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => Y z.1 z.2))
    (hR : ∃ R, ∀ σ y, R < ‖y‖ → Y σ y = 0) :
    MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure := by
  obtain ⟨R, hR⟩ := hR
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    hc.continuousOn
  refine memLp_of hc.aestronglyMeasurable ?_
  unfold periodLIntegral
  calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖Y σ y‖ ^ 2)
      ≤ ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, (Metric.closedBall (0 : Space) R).indicator
          (fun _ => ENNReal.ofReal (C ^ 2)) y := by
        refine setLIntegral_mono' measurableSet_Icc fun σ hσ => lintegral_mono fun y => ?_
        by_cases hy : y ∈ Metric.closedBall (0 : Space) R
        · rw [indicator_of_mem hy]
          exact ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ (norm_nonneg _) (hC (σ, y) ⟨hσ, hy⟩) 2)
        · rw [indicator_of_notMem hy]
          have hy' : R < ‖y‖ := by
            rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
            exact hy
          simp [hR σ y hy']
    _ < ⊤ := by
        rw [lintegral_indicator_const measurableSet_closedBall, lintegral_const,
          Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
          ENNReal.ofReal_lt_top

theorem slice_fderiv_apply {q : ℝ → Space → ℝ}
    (hq : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)) (σ : ℝ) (y v : Space) :
    fderiv ℝ (q σ) y v = fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) (σ, y) (0, v) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => q z.1 z.2) (σ, y) :=
    (hq.differentiable (by simp)) _
  have h := hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)
  rw [show q σ = (fun z : ℝ × Space => q z.1 z.2) ∘ fun y => (σ, y) from rfl, h.fderiv]
  rfl

theorem gradient_continuous {q : ℝ → Space → ℝ}
    (hq : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradientAt (q z.1) z.2) := by
  have e : (fun z : ℝ × Space => gradientAt (q z.1) z.2) = fun z => ∑ i : Fin 3,
      fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) z (0, unitVector i) • unitVector i := by
    funext z
    unfold gradientAt
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [slice_fderiv_apply hq]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((hq.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

theorem gradient_vanish {q : ℝ → Space → ℝ} {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → q σ y = 0) (σ : ℝ) (y : Space)
    (hy : R < ‖y‖) : gradientAt (q σ) y = 0 := by
  have hev : q σ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
    exact hR σ x hx
  unfold gradientAt
  rw [hev.fderiv_eq]
  simp

theorem pairing_sub {X₁ X₂ Y : ℝ → Space → Space}
    (h₁ : MemLp (fun z : ℝ × Space => X₁ z.1 z.2) 2 periodMeasure)
    (h₂ : MemLp (fun z : ℝ × Space => X₂ z.1 z.2) 2 periodMeasure)
    (hY : MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure) :
    ∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (X₁ σ y - X₂ σ y) (Y σ y) =
      (∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (X₁ σ y) (Y σ y)) -
        ∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (X₂ σ y) (Y σ y) := by
  have hi : ∀ {X : ℝ → Space → Space}, MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure →
      Integrable (fun z : ℝ × Space => inner ℝ (X z.1 z.2) (Y z.1 z.2)) periodMeasure := by
    intro X hX
    refine (L2.integrable_inner (𝕜 := ℝ) (toL2 X) (toL2 Y)).congr ?_
    filter_upwards [coeFn_toL2 hX, coeFn_toL2 hY] with z a b
    rw [a, b]
  have i1 := hi h₁
  have i2 := hi h₂
  have i3 : Integrable (fun z : ℝ × Space => inner ℝ (X₁ z.1 z.2 - X₂ z.1 z.2) (Y z.1 z.2))
      periodMeasure := by
    refine (i1.sub i2).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.sub_apply, inner_sub_left]
  rw [← integral_prod _ i1, ← integral_prod _ i2, ← integral_prod _ i3, ← integral_sub i1 i2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [inner_sub_left]

theorem solenoidalPart_unique {F Q Q' : ℝ → Space → Space} (h : IsSolenoidalPartOf F Q)
    (h' : IsSolenoidalPartOf F Q') : ∀ᵐ z : ℝ × Space, Q z.1 z.2 = Q' z.1 z.2 := by
  have m1 := memLp_of h.1 h.2.2.1
  have m2 := memLp_of h'.1 h'.2.2.1
  have hD := gradSolenoidalDensityHolds_proof (fun σ y => Q σ y - Q' σ y) (h.1.sub h'.1)
    (fun σ y => by simp only [h.2.1 σ y, h'.2.1 σ y]) (lt_top_of_memLp (m1.sub m2))
    (fun q hq => by
      obtain ⟨R, hR⟩ := hq.2.2
      have hY := memLp_of_continuous (gradient_continuous hq.1)
        ⟨R, fun σ y hy => gradient_vanish hR σ y hy⟩
      rw [pairing_sub m1 m2 hY, h.2.2.2.1 q hq, h'.2.2.2.1 q hq, sub_zero])
    (fun ψ hψ => by
      have hY := memLp_of_continuous hψ.1.continuous hψ.2.2.1
      rw [pairing_sub m1 m2 hY, h.2.2.2.2 ψ hψ, h'.2.2.2.2 ψ hψ, sub_self])
  filter_upwards [hD] with z hz
  exact sub_eq_zero.1 hz

end Internal.CurlGraphDensity

open Internal.CurlGraphDensity in
theorem curlGraphDensityHolds_proof : CurlGraphDensityHolds := by
  intro F Q hF hp hR hQ
  obtain ⟨Q', hQ', ψ, hψ, h1, h2⟩ := exists_solenoidalPart_approx F hF hp hR
  have hu := solenoidalPart_unique hQ hQ'
  refine ⟨ψ, hψ, ?_, h2⟩
  refine h1.congr fun n => (periodLIntegral_congr ?_).symm
  filter_upwards [hu] with z hz
  rw [hz]

end Breakdown.Coercive
