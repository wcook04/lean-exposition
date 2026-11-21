import Breakdown.CertTorus.DecayStatements
import Breakdown.Uniqueness.FundSolByParts
import Breakdown.Uniqueness.FundSolPointwiseAux2

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

private theorem cutoff_smooth (ρ : ℝ) : ContDiff ℝ ∞ (ballCutoff ρ) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

private theorem cutoff_one {ρ : ℝ} (hρ : 0 < ρ) {z : Space} (hz : ‖z‖ ≤ ρ) : ballCutoff ρ z = 1 := by
  unfold ballCutoff
  apply Real.smoothTransition.one_of_one_le
  have hsq : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hq : ‖z‖ ^ 2 / ρ ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hsq
  linarith

private theorem cutoff_zero {ρ : ℝ} (hρ : 0 < ρ) {z : Space} (hz : 2 * ρ < ‖z‖) : ballCutoff ρ z = 0 := by
  unfold ballCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have hsq : (2 * ρ) ^ 2 < ‖z‖ ^ 2 := pow_lt_pow_left₀ hz (by positivity) (by norm_num)
  have hq : 2 ≤ ‖z‖ ^ 2 / ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

private theorem truncated_smooth {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (ρ : ℝ) :
    ContDiff ℝ ∞ (fun z => ballCutoff ρ z * g z) :=
  (cutoff_smooth ρ).mul hg

private theorem truncated_compact {g : Space → ℝ} {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (fun z => ballCutoff ρ z * g z) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * ρ)) (fun z hz => ?_)
  have hz' : 2 * ρ < ‖z‖ := by
    simpa [mem_closedBall, dist_zero_right, not_le] using hz
  simp [cutoff_zero hρ hz']

private theorem integrable_decay_sq (D : ℝ) :
    Integrable (fun x : Space => (D / (1 + ‖x‖) ^ 2) ^ 2) := by
  have hdim : ((Module.finrank ℝ Space : ℕ) : ℝ) < 4 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hI := (integrable_one_add_norm (μ := (volume : Measure Space)) hdim).const_mul (D ^ 2)
  refine hI.congr (ae_of_all _ (fun x => ?_))
  have hpos : 0 < 1 + ‖x‖ := by positivity
  simp only
  rw [Real.rpow_neg hpos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

theorem pressureIdentification_of_harmonic :
    HarmonicGradientBound → TruncatedNewton → PressureIdentification := by
  intro hHG hTN q g A hq hg hLap hL2 hgA i y
  obtain ⟨C, hC⟩ := hHG
  obtain ⟨⟨D, hD⟩, hlim⟩ := hTN g A hg hgA
  set P : ℝ → Space → ℝ := fun ρ => FundSol.potential (fun z => ballCutoff ρ z * g z) with hP
  have hPs : ∀ ρ, 0 < ρ → ContDiff ℝ ∞ (P ρ) := fun ρ hρ =>
    FundSol.contDiff_potential (truncated_smooth hg ρ) (truncated_compact hρ)
  have hPl : ∀ ρ, 0 < ρ → ∀ x, FundSol.scalarSumSecondPartials (P ρ) x = ballCutoff ρ x * g x :=
    fun ρ hρ x => FundSol.scalarSumSecondPartials_potential (truncated_smooth hg ρ) (truncated_compact hρ) x
  have hqd : Differentiable ℝ q := FundSol.Internal.differentiable_of_smooth hq
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  set M : ℝ := ∫ x, (2 * ‖fderiv ℝ q x‖ ^ 2 + 2 * (D / (1 + ‖x‖) ^ 2) ^ 2) with hM
  have hMi : Integrable (fun x : Space => 2 * ‖fderiv ℝ q x‖ ^ 2 + 2 * (D / (1 + ‖x‖) ^ 2) ^ 2) := by
    have hq2 : Integrable (fun x : Space => ‖fderiv ℝ q x‖ ^ 2) := by
      have := hL2.integrable_norm_pow (p := 2) (by norm_num)
      simpa using this
    exact (hq2.const_mul 2).add ((integrable_decay_sq D).const_mul 2)
  have hbound : ∀ ρ, max 1 (‖y‖ + 1) ≤ ρ →
      |fderiv ℝ q y (unitVector i) + fderiv ℝ (P ρ) y (unitVector i)| ≤
        |C| * (ρ - ‖y‖) ^ (-(3 / 2 : ℝ)) * M ^ (1 / 2 : ℝ) := by
    intro ρ hρ
    have hρ1 : 1 ≤ ρ := le_trans (le_max_left _ _) hρ
    have hρy : ‖y‖ + 1 ≤ ρ := le_trans (le_max_right _ _) hρ
    have hρ0 : 0 < ρ := by linarith
    have hr : 0 < ρ - ‖y‖ := by linarith
    have hPd : Differentiable ℝ (P ρ) := FundSol.Internal.differentiable_of_smooth (hPs ρ hρ0)
    have hGs : ContDiff ℝ ∞ (q + P ρ) := hq.add (hPs ρ hρ0)
    have hfd : ∀ x, fderiv ℝ (q + P ρ) x = fderiv ℝ q x + fderiv ℝ (P ρ) x := fun x =>
      fderiv_add (hqd x) (hPd x)
    have hharm : ∀ x ∈ ball y (ρ - ‖y‖), FundSol.scalarSumSecondPartials (q + P ρ) x = 0 := by
      intro x hx
      have hxy : dist x y < ρ - ‖y‖ := hx
      have hxn : ‖x‖ ≤ ρ := by
        have := norm_le_norm_add_norm_sub' x y
        rw [dist_eq_norm] at hxy
        linarith
      have hsum : FundSol.scalarSumSecondPartials (q + P ρ) x =
          FundSol.scalarSumSecondPartials q x + FundSol.scalarSumSecondPartials (P ρ) x := by
        unfold FundSol.scalarSumSecondPartials FundSol.secondPartial
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [iteratedFDeriv_add_apply (hq.of_le h2).contDiffAt ((hPs ρ hρ0).of_le h2).contDiffAt]
        rfl
      rw [hsum, hLap x, hPl ρ hρ0 x, cutoff_one hρ0 hxn]
      ring
    have hgrad := hC (q + P ρ) y (ρ - ‖y‖) hr hGs hharm
    have hpt : ∀ x, ‖fderiv ℝ (q + P ρ) x‖ ^ 2 ≤
        2 * ‖fderiv ℝ q x‖ ^ 2 + 2 * (D / (1 + ‖x‖) ^ 2) ^ 2 := by
      intro x
      rw [hfd x]
      have htri := norm_add_le (fderiv ℝ q x) (fderiv ℝ (P ρ) x)
      have hPb : ‖fderiv ℝ (P ρ) x‖ ≤ D / (1 + ‖x‖) ^ 2 := hD ρ hρ1 x
      have hn1 := norm_nonneg (fderiv ℝ q x)
      have hn2 := norm_nonneg (fderiv ℝ (P ρ) x)
      have hn3 := norm_nonneg (fderiv ℝ q x + fderiv ℝ (P ρ) x)
      have hsq1 : ‖fderiv ℝ q x + fderiv ℝ (P ρ) x‖ ^ 2 ≤
          (‖fderiv ℝ q x‖ + ‖fderiv ℝ (P ρ) x‖) ^ 2 := pow_le_pow_left₀ hn3 htri 2
      have hsq2 : ‖fderiv ℝ (P ρ) x‖ ^ 2 ≤ (D / (1 + ‖x‖) ^ 2) ^ 2 := pow_le_pow_left₀ hn2 hPb 2
      nlinarith [sq_nonneg (‖fderiv ℝ q x‖ - ‖fderiv ℝ (P ρ) x‖)]
    have hint : ∫ x in ball y (ρ - ‖y‖), ‖fderiv ℝ (q + P ρ) x‖ ^ 2 ≤ M := by
      calc ∫ x in ball y (ρ - ‖y‖), ‖fderiv ℝ (q + P ρ) x‖ ^ 2
          ≤ ∫ x in ball y (ρ - ‖y‖), (2 * ‖fderiv ℝ q x‖ ^ 2 + 2 * (D / (1 + ‖x‖) ^ 2) ^ 2) :=
            integral_mono_of_nonneg (ae_of_all _ (fun x => by positivity)) hMi.integrableOn
              (ae_of_all _ hpt)
        _ ≤ M := setIntegral_le_integral hMi (ae_of_all _ (fun x => by positivity))
    have hI0 : 0 ≤ ∫ x in ball y (ρ - ‖y‖), ‖fderiv ℝ (q + P ρ) x‖ ^ 2 :=
      integral_nonneg (fun x => by positivity)
    have hroot : (∫ x in ball y (ρ - ‖y‖), ‖fderiv ℝ (q + P ρ) x‖ ^ 2) ^ (1 / 2 : ℝ) ≤
        M ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hI0 hint (by norm_num)
    have hroot0 : 0 ≤ (∫ x in ball y (ρ - ‖y‖), ‖fderiv ℝ (q + P ρ) x‖ ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hI0 _
    have hpow0 : 0 ≤ (ρ - ‖y‖) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hr.le _
    have happ : |fderiv ℝ q y (unitVector i) + fderiv ℝ (P ρ) y (unitVector i)| ≤
        ‖fderiv ℝ (q + P ρ) y‖ := by
      rw [hfd y]
      have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
      have := (fderiv ℝ q y + fderiv ℝ (P ρ) y).le_opNorm (unitVector i)
      rw [hu, mul_one] at this
      simpa [Real.norm_eq_abs] using this
    calc |fderiv ℝ q y (unitVector i) + fderiv ℝ (P ρ) y (unitVector i)|
        ≤ ‖fderiv ℝ (q + P ρ) y‖ := happ
      _ ≤ C * (ρ - ‖y‖) ^ (-(3 / 2 : ℝ)) *
          (∫ x in ball y (ρ - ‖y‖), ‖fderiv ℝ (q + P ρ) x‖ ^ 2) ^ (1 / 2 : ℝ) := hgrad
      _ ≤ |C| * (ρ - ‖y‖) ^ (-(3 / 2 : ℝ)) *
          (∫ x in ball y (ρ - ‖y‖), ‖fderiv ℝ (q + P ρ) x‖ ^ 2) ^ (1 / 2 : ℝ) := by
            gcongr
            exact le_abs_self C
      _ ≤ |C| * (ρ - ‖y‖) ^ (-(3 / 2 : ℝ)) * M ^ (1 / 2 : ℝ) := by
            gcongr
  have hmaj : Tendsto (fun ρ : ℝ => |C| * (ρ - ‖y‖) ^ (-(3 / 2 : ℝ)) * M ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => ρ - ‖y‖) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    have h2' : Tendsto (fun ρ : ℝ => (ρ - ‖y‖) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp h1
    have := (h2'.const_mul |C|).mul_const (M ^ (1 / 2 : ℝ))
    simpa using this
  have hzero : Tendsto (fun ρ : ℝ => fderiv ℝ q y (unitVector i) + fderiv ℝ (P ρ) y (unitVector i))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (max 1 (‖y‖ + 1))] with ρ hρ
    rw [Real.norm_eq_abs]
    exact hbound ρ hρ
  have hsum : Tendsto (fun ρ : ℝ => fderiv ℝ q y (unitVector i) + fderiv ℝ (P ρ) y (unitVector i))
      atTop (𝓝 (fderiv ℝ q y (unitVector i) + newtonGradientComp g i y)) :=
    tendsto_const_nhds.add (hlim i y)
  have heq := tendsto_nhds_unique hsum hzero
  linarith

end Breakdown.FarField
