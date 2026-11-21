import TorusEuler.Maximality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace TorusEuler

private theorem ball_origin_subset_centeredCell :
    Metric.ball (0 : Vec3) (1 / 2) ⊆ centeredCell := by
  intro x hx i
  have hnorm : ‖x‖ < (1 / 2 : ℝ) := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  exact abs_le.mp (hi.trans hnorm.le)

/-- The essential spatial supremum controls the value of a continuous field at the origin. -/
theorem ofReal_norm_zero_le_torusLInf {E : Type*} [NormedAddCommGroup E]
    {f : Vec3 → E} (hf : Continuous f) : ENNReal.ofReal ‖f 0‖ ≤ torusLInf f := by
  by_contra! h
  let U := Metric.ball (0 : Vec3) (1 / 2) ∩ {x | torusLInf f < ENNReal.ofReal ‖f x‖}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (ENNReal.continuous_ofReal.comp hf.norm))
  have hzero : (0 : Vec3) ∈ U := ⟨Metric.mem_ball_self (by norm_num), h⟩
  have hsub : U ⊆ centeredCell := fun _ hx => ball_origin_subset_centeredCell hx.1
  have hpos : 0 < (volume : Measure Vec3) U := hU.measure_pos _ ⟨0, hzero⟩
  have hae : ∀ᵐ x ∂(volume : Measure Vec3).restrict centeredCell,
      ENNReal.ofReal ‖f x‖ ≤ torusLInf f := by
    simpa only [ofReal_norm, torusLInf] using
      (ae_le_eLpNormEssSup (f := f) (μ := (volume : Measure Vec3).restrict centeredCell))
  have hnull : (volume : Measure Vec3).restrict centeredCell U = 0 := by
    have hn : ∀ᵐ x ∂(volume : Measure Vec3).restrict centeredCell, x ∉ U :=
      hae.mono fun _ hx hxU => (not_lt_of_ge hx) hxU.2
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hn
  rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.mpr hsub] at hnull
  exact hpos.ne' hnull

theorem ofReal_norm_curl_zero_le_torusLInf {v : Vec3 → Vec3} (hv : ContDiff ℝ 1 v) :
    ENNReal.ofReal ‖curl v 0‖ ≤ torusLInf (curl v) :=
  ofReal_norm_zero_le_torusLInf (continuous_curlOfDerivative.comp (hv.continuous_fderiv one_ne_zero))

/-- A whole interval with a lower bound on central curl gives a lower bound
for the time integral of the essential supremum. -/
theorem curlIntegral_lower_bound_on_interval {T a b m : ℝ} {u : Velocity}
    (ha : 0 ≤ a) (hb : b ≤ T) (hm : 0 ≤ m)
    (hsmooth : ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (u t))
    (hcurl : ∀ t ∈ Ico a b, m ≤ ‖curl (u t) 0‖) :
    ENNReal.ofReal (m * (b - a)) ≤ ∫⁻ t in Ico 0 T, torusLInf (curl (u t)) := by
  have hsub : Ico a b ⊆ Ico 0 T := Ico_subset_Ico ha hb
  calc
    ENNReal.ofReal (m * (b - a)) = ∫⁻ _ in Ico a b, ENNReal.ofReal m := by
      rw [setLIntegral_const, Real.volume_Ico, ENNReal.ofReal_mul hm]
    _ ≤ ∫⁻ t in Ico a b, torusLInf (curl (u t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      exact (ENNReal.ofReal_le_ofReal (hcurl t ht)).trans
        (ofReal_norm_curl_zero_le_torusLInf (hsmooth t (hsub ht)))
    _ ≤ ∫⁻ t in Ico 0 T, torusLInf (curl (u t)) := lintegral_mono_set hsub

private theorem activationInterval_curl_mass {c C l s r δ : ℝ} (hc : 0 < c)
    (hC : 0 < C) (hl : 0 < l) (hδ : 0 ≤ δ)
    (hcross : 2 * l ^ 2 ≤ r * δ) (hspeed : r ≤ C * s * l) :
    (2 * c / C) * l ≤ (c * s) * δ := by
  have h : 2 * l ≤ C * (s * δ) := by
    apply (mul_le_mul_iff_left₀ hl).mp
    calc
      (2 * l) * l = 2 * l ^ 2 := by ring
      _ ≤ r * δ := hcross
      _ ≤ (C * s * l) * δ := mul_le_mul_of_nonneg_right hspeed hδ
      _ = (C * (s * δ)) * l := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  calc
    2 * c * l = c * (2 * l) := by ring
    _ ≤ c * (C * (s * δ)) := mul_le_mul_of_nonneg_left h hc.le
    _ = (c * s * δ) * C := by ring

/-- Direct proof of the curl integral in Corollary 8.3 from Sections 7 and 8.
The normalized crossing time is at least `2 * L j ^ 2`. The factor
`μ j ^ (1/8)` cancels between the speed upper bound and the curl lower bound. -/
theorem curlIntegral_eq_top_of_activation_bounds {T c C : ℝ} {u : Velocity}
    {t μ L r : ℕ → ℝ} (hc : 0 < c) (hC : 0 < C) (ht : Monotone t)
    (hL : Tendsto L atTop atTop) (hsmooth : ∀ s ∈ Ico 0 T, ContDiff ℝ 1 (u s))
    (hbounds : ∀ᶠ j in atTop, 0 ≤ t j ∧ t (j + 1) ≤ T ∧ 0 < μ j ∧
      2 * L j ^ 2 ≤ r j * (t (j + 1) - t j) ∧
      r j ≤ C * μ j ^ (1 / 8 : ℝ) * L j ∧
      ∀ s ∈ Ico (t j) (t (j + 1)), c * μ j ^ (1 / 8 : ℝ) ≤ ‖curl (u s) 0‖) :
    (∫⁻ s in Ico 0 T, torusLInf (curl (u s))) = ⊤ := by
  let I := ∫⁻ s in Ico 0 T, torusLInf (curl (u s))
  change I = ⊤
  by_contra hI
  have hcoef : 0 < 2 * c / C := div_pos (mul_pos (by norm_num) hc) hC
  have hlarge := (hL.const_mul_atTop hcoef).eventually_ge_atTop (I.toReal + 1)
  have hLpos := hL.eventually_ge_atTop (1 : ℝ)
  obtain ⟨j, ⟨haj, hbj, hμj, hcross, hspeed, hcurl⟩, hj, hLj⟩ :=
    (hbounds.and (hlarge.and hLpos)).exists
  have hmass := activationInterval_curl_mass hc hC (zero_lt_one.trans_le hLj)
    (sub_nonneg.mpr (ht (Nat.le_succ j))) hcross hspeed
  have hbound := curlIntegral_lower_bound_on_interval haj hbj
    (mul_nonneg hc.le (Real.rpow_nonneg hμj.le _)) hsmooth hcurl
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hI).mp
    ((ENNReal.ofReal_le_ofReal hmass).trans hbound)
  exact (not_le_of_gt (lt_add_one _)) (hj.trans hreal)

/-- The logarithmic scale of the frequency schedule tends to infinity. -/
theorem terminalLogScale_tendsto_atTop {freq : ℕ → ℝ} (hfreq : Tendsto freq atTop atTop) :
    Tendsto (fun j => 4 * Real.log (freq (j + 1))) atTop atTop := by
  have hnext : Tendsto (fun j : ℕ => j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => Nat.le_succ j) tendsto_id
  exact (Real.tendsto_log_atTop.comp (hfreq.comp hnext)).const_mul_atTop (by norm_num)

/-- The lower-order terms in the central curl estimate can absorb at most half
of the leading power for sufficiently large frequencies. -/
theorem eventually_half_curl_power_lower_bound {c B : ℝ} {μ : ℕ → ℝ}
    (hc : 0 < c) (hμ : Tendsto μ atTop atTop) :
    ∀ᶠ j in atTop, (c / 2) * μ j ^ (1 / 8 : ℝ) ≤
      c * μ j ^ (1 / 8 : ℝ) - B * μ j ^ (1 / 32 : ℝ) - B := by
  have hgap := ((tendsto_rpow_atTop (by norm_num : 0 < (3 / 32 : ℝ))).comp hμ).eventually_ge_atTop
    (4 * B / c)
  have hmain := ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 8 : ℝ))).comp hμ).eventually_ge_atTop
    (4 * B / c)
  filter_upwards [hμ.eventually_gt_atTop 0, hgap, hmain] with j hjμ hjgap hjmain
  have hpower : μ j ^ (3 / 32 : ℝ) * μ j ^ (1 / 32 : ℝ) = μ j ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add hjμ]
    norm_num
  have hb₁ : B ≤ (c / 4) * μ j ^ (3 / 32 : ℝ) := by
    change 4 * B / c ≤ μ j ^ (3 / 32 : ℝ) at hjgap
    nlinarith only [(div_le_iff₀ hc).mp hjgap]
  have hb₂ : B ≤ (c / 4) * μ j ^ (1 / 8 : ℝ) := by
    change 4 * B / c ≤ μ j ^ (1 / 8 : ℝ) at hjmain
    nlinarith only [(div_le_iff₀ hc).mp hjmain]
  have herror : B * μ j ^ (1 / 32 : ℝ) ≤ (c / 4) * μ j ^ (1 / 8 : ℝ) := by
    rw [← hpower, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hb₁ (Real.rpow_nonneg hjμ.le _)
  linarith only [herror, hb₂]

/-- The lower bound before absorbing the older gradients and uniformly bounded errors in
Section 8 suffices for the direct curl-integral argument. -/
theorem curlIntegral_eq_top_of_activation_bounds_with_errors {T c C B : ℝ} {u : Velocity}
    {t μ L r : ℕ → ℝ} (hc : 0 < c) (hC : 0 < C) (ht : Monotone t)
    (hμ : Tendsto μ atTop atTop) (hL : Tendsto L atTop atTop)
    (hsmooth : ∀ s ∈ Ico 0 T, ContDiff ℝ 1 (u s))
    (hbounds : ∀ᶠ j in atTop, 0 ≤ t j ∧ t (j + 1) ≤ T ∧
      2 * L j ^ 2 ≤ r j * (t (j + 1) - t j) ∧
      r j ≤ C * μ j ^ (1 / 8 : ℝ) * L j ∧
      ∀ s ∈ Ico (t j) (t (j + 1)), c * μ j ^ (1 / 8 : ℝ) - B * μ j ^ (1 / 32 : ℝ) - B
        ≤ ‖curl (u s) 0‖) :
    (∫⁻ s in Ico 0 T, torusLInf (curl (u s))) = ⊤ := by
  apply curlIntegral_eq_top_of_activation_bounds (half_pos hc) hC ht hL hsmooth
  filter_upwards [hbounds, hμ.eventually_gt_atTop 0,
    eventually_half_curl_power_lower_bound hc (B := B) hμ] with j hj hjμ hpower
  obtain ⟨haj, hbj, hcross, hspeed, hcurl⟩ := hj
  exact ⟨haj, hbj, hjμ, hcross, hspeed, fun s hs => hpower.trans (hcurl s hs)⟩

end TorusEuler
