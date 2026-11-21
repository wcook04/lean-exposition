import Breakdown.Cert.CoerciveSmoothApproxClass
import Breakdown.Cert.CoerciveSmoothApproxLimitsWhole

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem period_add_of_measurable {F : ℝ × Space → ℝ≥0∞} (hF : Measurable F)
    (g : ℝ → Space → ℝ≥0∞) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (F (σ, y) + g σ y) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, F (σ, y)) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y := by
  calc _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ((∫⁻ y, F (σ, y)) + ∫⁻ y, g σ y) :=
        lintegral_congr fun σ =>
          lintegral_add_left (f := fun y => F (σ, y)) (hF.comp measurable_prodMk_left) _
    _ = _ := lintegral_add_left (f := fun σ => ∫⁻ y, F (σ, y))
        (hF.lintegral_prod_right' (ν := (volume : Measure Space))) _

theorem moment_kernel_contDiff (n : ℕ) (k : Fin 3) :
    ContDiff ℝ ∞ (fun t : ℝ × Space => t.2 k * kernel n t) := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ × Space => t.2 k) := by fun_prop
  exact h1.mul (kernel_contDiff n)

theorem moment_kernel_hasCompactSupport (n : ℕ) (k : Fin 3) :
    HasCompactSupport (fun t : ℝ × Space => t.2 k * kernel n t) :=
  (kernel_hasCompactSupport n).mul_left

theorem moment_kernel_lintegral_le (n : ℕ) (k : Fin 3) :
    ∫⁻ t, ‖t.2 k * kernel n t‖ₑ ≤ ENNReal.ofReal (2 / ((n : ℝ) + 1)) := by
  calc ∫⁻ t, ‖t.2 k * kernel n t‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (2 / ((n : ℝ) + 1)) * ‖kernel n t‖ₑ :=
        lintegral_mono fun t => by
          by_cases hk : kernel n t = 0
          · simp [hk]
          have ht := mem_ball_zero_iff.1 (kernel_support_subset_ball n hk)
          have h1 : ‖t.2 k‖ ≤ 2 / ((n : ℝ) + 1) :=
            ((PiLp.norm_apply_le t.2 k).trans (norm_snd_le t)).trans ht.le
          rw [enorm_mul]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (2 / ((n : ℝ) + 1)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_kernel_eq_one, mul_one]

theorem transport_pointwise (D B0 B1 B2 : Space) :
    ‖D + (1 / 2 : ℝ) • (B0 + B1 + B2)‖ ^ 2 ≤
      ‖B0‖ ^ 2 + (‖B1‖ ^ 2 + (‖B2‖ ^ 2 + 4 * ‖D‖ ^ 2)) := by
  have h1 : ‖D + (1 / 2 : ℝ) • (B0 + B1 + B2)‖ ≤
      ‖D‖ + (1 / 2 : ℝ) * ‖B0‖ + (1 / 2 : ℝ) * ‖B1‖ + (1 / 2 : ℝ) * ‖B2‖ := by
    calc ‖D + (1 / 2 : ℝ) • (B0 + B1 + B2)‖ ≤ ‖D‖ + ‖(1 / 2 : ℝ) • (B0 + B1 + B2)‖ := norm_add_le _ _
      _ = ‖D‖ + (1 / 2 : ℝ) * ‖B0 + B1 + B2‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      _ ≤ ‖D‖ + (1 / 2 : ℝ) * (‖B0‖ + ‖B1‖ + ‖B2‖) := by
          gcongr
          exact norm_add₃_le
      _ = _ := by ring
  have h0 := norm_nonneg (D + (1 / 2 : ℝ) • (B0 + B1 + B2))
  have hsq := pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg (‖D‖ - (1 / 2 : ℝ) * ‖B0‖), sq_nonneg (‖D‖ - (1 / 2 : ℝ) * ‖B1‖),
    sq_nonneg (‖D‖ - (1 / 2 : ℝ) * ‖B2‖), sq_nonneg ((1 / 2 : ℝ) * ‖B0‖ - (1 / 2 : ℝ) * ‖B1‖),
    sq_nonneg ((1 / 2 : ℝ) * ‖B0‖ - (1 / 2 : ℝ) * ‖B2‖),
    sq_nonneg ((1 / 2 : ℝ) * ‖B1‖ - (1 / 2 : ℝ) * ‖B2‖)]

theorem transport_tendsto_of_eq {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (heq : ∀ n σ y, transportPart P (mollify n v) σ y =
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) (σ, y) +
        (1 / 2 : ℝ) • ∑ k : Fin 3, ((fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          volume] joint (fun s x => G s x (unitVector k))) (σ, y)) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖transportPart P (mollify n v) σ y - g σ y‖ ^ 2))
      atTop (𝓝 0) := by
  have hH := volume_prod_invariantClass
  have hGl : LocallyIntegrable (joint G) volume := PerturbationFacts.gradient_locallyIntegrable hv
  set C := periodLIntegral (fun σ y => ‖G σ y‖ ^ 2) with hCdef
  have hCf : C < ⊤ := gradient_sq_lt_top hv
  set E : ℕ → ℝ≥0∞ := fun n => periodLIntegral (fun σ y =>
    ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) (σ, y) - g σ y‖ ^ 2) with hEdef
  have hEt : Tendsto E atTop (𝓝 0) := period_convolution_sq_tendsto hv.measurable_derivative
    hv.periodic_derivative hv.derivative_finite
  set r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 / ((n : ℝ) + 1)) with hrdef
  have hr : Tendsto r atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simpa [div_eq_mul_inv] using this
  have hlim : Tendsto (fun n => r n ^ 2 * C + (r n ^ 2 * C + (r n ^ 2 * C +
      ENNReal.ofReal 4 * E n))) atTop (𝓝 0) := by
    have a1 : Tendsto (fun n => r n ^ 2) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_pow 2).tendsto 0).comp hr
      simpa [Function.comp_def] using this
    have a2 := ENNReal.Tendsto.mul_const a1 (Or.inr hCf.ne)
    have a4 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 4) hEt (Or.inr ENNReal.ofReal_ne_top)
    simpa using a2.add (a2.add (a2.add a4))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    (fun n => ?_)
  set B : Fin 3 → ℝ × Space → Space := fun k =>
    (fun t : ℝ × Space => t.2 k * kernel n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      joint (fun s x => G s x (unitVector k)) with hBdef
  have hBc : ∀ k, Continuous (B k) := fun k =>
    ((moment_kernel_hasCompactSupport n k).contDiff_convolution_left _ (moment_kernel_contDiff n k)
      (joint_apply_locallyIntegrable hGl _)).continuous
  have hBm : ∀ k, Measurable (fun z : ℝ × Space => ENNReal.ofReal (‖B k z‖ ^ 2)) := fun k =>
    (((hBc k).norm.pow 2).measurable).ennreal_ofReal
  have hBb : ∀ k, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖B k (σ, y)‖ ^ 2) ≤ r n ^ 2 * C := by
    intro k
    have hmeas : AEStronglyMeasurable (joint (fun s x => G s x (unitVector k))) volume :=
      (ContinuousLinearMap.apply ℝ Space (unitVector k)).continuous.comp_aestronglyMeasurable
        hv.measurable_gradient
    have hy := period_convolution_sq_le (moment_kernel_contDiff n k).continuous
      (moment_kernel_hasCompactSupport n k) hmeas
      (fun σ y => by simp only [hv.periodic_gradient σ y])
    have hGk : periodLIntegral (fun σ y => ‖G σ y (unitVector k)‖ ^ 2) ≤ C :=
      lintegral_mono fun σ => lintegral_mono fun y => by
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
        have := (G σ y).le_opNorm (unitVector k)
        rwa [PerturbationFacts.norm_unitVector_eq, mul_one] at this
    calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖B k (σ, y)‖ ^ 2)
        = periodLIntegral (fun σ y => ‖∫ t, (t.2 k * kernel n t) •
            joint (fun s x => G s x (unitVector k)) ((σ, y) - t)‖ ^ 2) := by
          unfold periodLIntegral
          simp only [hBdef, convolution_def, ContinuousLinearMap.lsmul_apply]
      _ ≤ (∫⁻ t, ‖t.2 k * kernel n t‖ₑ) ^ 2 *
            periodLIntegral (fun σ y => ‖G σ y (unitVector k)‖ ^ 2) := hy
      _ ≤ r n ^ 2 * C := by
          gcongr
          exact moment_kernel_lintegral_le n k
  have hpt : ∀ σ y, ENNReal.ofReal (‖transportPart P (mollify n v) σ y - g σ y‖ ^ 2) ≤
      ENNReal.ofReal (‖B 0 (σ, y)‖ ^ 2) + (ENNReal.ofReal (‖B 1 (σ, y)‖ ^ 2) +
        (ENNReal.ofReal (‖B 2 (σ, y)‖ ^ 2) + ENNReal.ofReal 4 * ENNReal.ofReal
          (‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) (σ, y) - g σ y‖ ^ 2))) := by
    intro σ y
    have e : transportPart P (mollify n v) σ y - g σ y =
        ((kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) (σ, y) - g σ y) +
          (1 / 2 : ℝ) • (B 0 (σ, y) + B 1 (σ, y) + B 2 (σ, y)) := by
      rw [heq n σ y, Fin.sum_univ_three]
      simp only [hBdef]
      abel
    rw [e, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (transport_pointwise _ _ _ _)
  calc periodLIntegral (fun σ y => ‖transportPart P (mollify n v) σ y - g σ y‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (ENNReal.ofReal (‖B 0 (σ, y)‖ ^ 2) +
          (ENNReal.ofReal (‖B 1 (σ, y)‖ ^ 2) + (ENNReal.ofReal (‖B 2 (σ, y)‖ ^ 2) +
            ENNReal.ofReal 4 * ENNReal.ofReal
              (‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint g) (σ, y) - g σ y‖ ^ 2)))) :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
    _ = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖B 0 (σ, y)‖ ^ 2)) +
          ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖B 1 (σ, y)‖ ^ 2)) +
          ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖B 2 (σ, y)‖ ^ 2)) +
            ENNReal.ofReal 4 * E n)) := by
        rw [period_add_of_measurable (hBm 0), period_add_of_measurable (hBm 1),
          period_add_of_measurable (hBm 2)]
        congr 3
        simp only [hEdef, periodLIntegral]
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ r n ^ 2 * C + (r n ^ 2 * C + (r n ^ 2 * C + ENNReal.ofReal 4 * E n)) := by
        gcongr
        · exact hBb 0
        · exact hBb 1
        · exact hBb 2

end Internal.SmoothApprox

end Coercive

end Breakdown
