import Breakdown.Frac.StSpace

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem forced_integral_pressureDefect_eq_zero
    (h2 : ForcedPressureMollifyStatement) (h3 : ForcedPressureAverageStatement)
    {T : ℝ} {v : ℝ → Space → Space} {q : ℝ → Space → ℝ} {F : ℝ → Space → Space}
    (hv : IsForcedSolutionOn T v q F) (hE : EnergyBoundedOn T v)
    {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) {t₁ t₂ : ℝ}
    (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ T) :
    ∫ t in t₁..t₂, pressureDefect v q t ϕ = 0 := by
  have hlim := h3 T v q F hv hE ϕ hϕ hc t₁ t₂ h₁ h₁₂ h₂
  have heq : ∀ ρ : ℝ, 0 < ρ →
      ∫ t in t₁..t₂, pressureDefect v q t (FundSol.mollify ρ ϕ)
        = ∫ t in t₁..t₂, pressureDefect v q t ϕ := by
    intro ρ hρ
    rw [intervalIntegral.integral_of_le h₁₂, intervalIntegral.integral_of_le h₁₂,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro t ht
    exact h2 T v q F hv hE t ⟨lt_of_le_of_lt h₁ ht.1, lt_of_lt_of_le ht.2 h₂⟩ ϕ hϕ hc ρ hρ
  have hconst : Filter.Tendsto
      (fun ρ : ℝ => ∫ t in t₁..t₂, pressureDefect v q t (FundSol.mollify ρ ϕ))
      Filter.atTop (nhds (∫ t in t₁..t₂, pressureDefect v q t ϕ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact (heq ρ hρ).symm
  exact tendsto_nhds_unique hconst hlim

theorem forcedPressureIdentity_of (h1 : ForcedPressureContinuityStatement)
    (h2 : ForcedPressureMollifyStatement) (h3 : ForcedPressureAverageStatement) :
    ForcedPressureIdentityStatement := by
  intro T v q F hv hE t ht ϕ hϕ hc
  have hcont := h1 T v q F hv hE ϕ hϕ hc
  have hsub : Ioo 0 T ⊆ Icc 0 T := Ioo_subset_Icc_self
  have hcontIoo : ContinuousOn (fun s => pressureDefect v q s ϕ) (Ioo 0 T) := hcont.mono hsub
  have hint : IntervalIntegrable (fun s => pressureDefect v q s ϕ) volume 0 t := by
    refine (hcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le ht.1.le]
    exact Icc_subset_Icc le_rfl ht.2.le
  have hmeas : StronglyMeasurableAtFilter (fun s => pressureDefect v q s ϕ) (nhds t) :=
    hcontIoo.stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hca : ContinuousAt (fun s => pressureDefect v q s ϕ) t :=
    hcontIoo.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint hmeas hca
  have hzero : (fun u => ∫ s in (0 : ℝ)..u, pressureDefect v q s ϕ) =ᶠ[nhds t]
      fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact forced_integral_pressureDefect_eq_zero h2 h3 hv hE hϕ hc le_rfl hu.1.le hu.2.le
  have hderiv0 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, pressureDefect v q s ϕ) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hzero
  exact hderiv.unique hderiv0

end Breakdown
