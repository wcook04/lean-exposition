import TorusEuler.ActivationTimes
import TorusEuler.PeriodicLift
import TorusEuler.TerminalCurlIntegral
import TorusEuler.TerminalIntegrals

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace TorusEuler

/-- Transfer the lower bound in (8.2) to the limiting curl on every activation interval.
The supplied spatial derivative errors tend to zero uniformly on those intervals. -/
theorem terminalCurl_tendsto_atTop_of_activationBounds {t : ℕ → ℝ} {T : ℝ}
    {U : ℕ → Velocity} {u : Velocity} {b e : ℕ → ℝ}
    (htlim : Tendsto t atTop (𝓝 T)) (ht : ∀ j, t j < T)
    (hb : Tendsto b atTop atTop) (he : Tendsto e atTop (𝓝 0))
    (hcurl : ∀ᶠ j in atTop, ∀ r ∈ Ico (t j) (t (j + 1)), b j ≤ ‖curl (U j r) 0‖)
    (herror : ∀ᶠ j in atTop, ∀ r ∈ Ico (t j) (t (j + 1)),
      ‖fderiv ℝ (u r) 0 - fderiv ℝ (U j r) 0‖ ≤ e j) :
    Tendsto (fun r => ‖curl (u r) 0‖) (𝓝[Ico 0 T] T) atTop := by
  let C : ℝ := ‖curlOfDerivativeCLM‖
  have hC : 0 ≤ C := norm_nonneg curlOfDerivativeCLM
  have hlower : Tendsto (fun j => b j - C * e j) atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [hb.eventually_ge_atTop (B + C), he.eventually (Iio_mem_nhds (zero_lt_one' ℝ))]
      with j hj hj'
    have h := mul_le_mul_of_nonneg_left (show e j ≤ 1 from hj'.le) hC
    change B ≤ b j - C * e j
    linarith
  have htransfer : ∀ᶠ j in atTop, ∀ r ∈ Ico (t j) (t (j + 1)),
      b j - C * e j ≤ ‖curl (u r) 0‖ := by
    filter_upwards [hcurl, herror] with j hjcurl hjerr
    intro r hr
    have hnorm : ‖curl (U j r) 0 - curl (u r) 0‖ ≤ C * e j := by
      rw [norm_sub_rev]
      have h := curlOfDerivativeCLM.le_opNorm (fderiv ℝ (u r) 0 - fderiv ℝ (U j r) 0)
      rw [map_sub] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hjerr r hr) hC)
    have htriangle := norm_sub_norm_le (curl (U j r) 0) (curl (u r) 0)
    linarith only [hjcurl r hr, hnorm, htriangle]
  exact (tendsto_atTop_of_activationBounds htlim ht hlower htransfer).mono_left
    (nhdsWithin_mono _ Ico_subset_Iio_self)

/-- A continuous extension to the closed centered-cell time slab gives the velocity bound
in Proposition 8.2 and Theorem 1.1. -/
theorem terminalVelocityBound_of_extension {T : ℝ} {u w : Velocity}
    (hw : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ centeredCell))
    (hagree : ∀ t ∈ Ico 0 T, ∀ x ∈ centeredCell, u t x = w t x) :
    ∃ B : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_centeredCell).exists_bound_of_continuousOn hw
  refine ⟨B, fun t ht => eLpNormEssSup_le_of_ae_bound ?_⟩
  filter_upwards [ae_restrict_mem isCompact_centeredCell.measurableSet] with x hx
  rw [hagree t ht x hx]
  exact hB (t, x) ⟨Ico_subset_Icc_self ht, hx⟩

/-- Assemble the terminal conclusions directly from the quantitative activation estimates.
The constructed solution, the off-origin limits and the activation bounds are inputs. -/
theorem theorem11_of_quantitative_activation_bounds {T c C B : ℝ} {u w : Velocity} {p : Pressure}
    {t μ L r : ℕ → ℝ} (hu : IsEulerSolution T u p)
    (hodd : ∀ s ∈ Ico 0 T, Function.Odd (u s))
    (hw : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ centeredCell))
    (hagree : ∀ s ∈ Ico 0 T, ∀ x ∈ centeredCell, u s x = w s x)
    (huLimit : HasOffOriginLimits T u) (hdtLimit : HasOffOriginLimits T (timeDerivative T u))
    (hc : 0 < c) (hC : 0 < C) (ht : Monotone t) (htlim : Tendsto t atTop (𝓝 T))
    (htbelow : ∀ j, t j < T) (hμ : Tendsto μ atTop atTop) (hL : Tendsto L atTop atTop)
    (hbounds : ∀ᶠ j in atTop, 0 ≤ t j ∧
      2 * L j ^ 2 ≤ r j * (t (j + 1) - t j) ∧
      r j ≤ C * μ j ^ (1 / 8 : ℝ) * L j ∧
      ∀ s ∈ Ico (t j) (t (j + 1)), c * μ j ^ (1 / 8 : ℝ) - B * μ j ^ (1 / 32 : ℝ) - B
        ≤ ‖curl (u s) 0‖) : Theorem11 := by
  have hcurl : (∫⁻ s in Ico 0 T, torusLInf (curl (u s))) = ⊤ := by
    apply curlIntegral_eq_top_of_activation_bounds_with_errors hc hC ht hμ hL
      (fun s hs => (hu.contDiff_velocity_slice hs).of_le (by simp))
    filter_upwards [hbounds] with j hj
    exact ⟨hj.1, (htbelow (j + 1)).le, hj.2⟩
  have hpower : Tendsto (fun j => (c / 2) * μ j ^ (1 / 8 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 8 : ℝ))).comp hμ).const_mul_atTop (half_pos hc)
  have hlower : ∀ᶠ j in atTop, ∀ s ∈ Ico (t j) (t (j + 1)),
      (c / 2) * μ j ^ (1 / 8 : ℝ) ≤ ‖curl (u s) 0‖ := by
    filter_upwards [eventually_half_curl_power_lower_bound hc (B := B) hμ, hbounds]
      with j hsmall hj
    exact fun s hs => hsmall.trans (hj.2.2.2 s hs)
  have hcentral : Tendsto (fun s => ‖curl (u s) 0‖) (𝓝[Ico 0 T] T) atTop :=
    (tendsto_atTop_of_activationBounds htlim htbelow hpower hlower).mono_left
    (nhdsWithin_mono _ Ico_subset_Iio_self)
  exact theorem11_of_solution_and_terminal_bounds hu hodd
    (terminalVelocityBound_of_extension hw hagree) hcentral huLimit hdtLimit hcurl

end TorusEuler
