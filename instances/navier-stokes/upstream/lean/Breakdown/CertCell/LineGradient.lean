import Breakdown.CertCell.SixthPowerStatements

open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

private lemma two_abs_le_integral_abs_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (b : ℝ) : 2 * |g b| ≤ ∫ t, |deriv g t| := by
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hg.differentiable one_ne_zero x).hasDerivAt
  have hint : Integrable (deriv g) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h := hc
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at h
    exact (h.filter_mono atTop_le_cocompact).tendsto
  have h1 : ∫ x in Iic b, deriv g x = g b := hc.integral_Iic_deriv_eq hg b
  have h2 : ∫ x in Ioi b, deriv g x = 0 - g b :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hint.integrableOn hlim
  have e1 : |g b| ≤ ∫ x in Iic b, |deriv g x| := by
    rw [← h1]
    exact abs_integral_le_integral_abs
  have e2 : |g b| ≤ ∫ x in Ioi b, |deriv g x| := by
    have h3 : |g b| = |∫ x in Ioi b, deriv g x| := by
      rw [h2, zero_sub, abs_neg]
    rw [h3]
    exact abs_integral_le_integral_abs
  have hsplit : ∫ t, |deriv g t| =
      (∫ x in Iic b, |deriv g x|) + ∫ x in Ioi b, |deriv g x| := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := b),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.abs.integrableOn
        hint.abs.integrableOn]
  linarith

private lemma unitVector_ne_zero (i : Fin 3) : unitVector i ≠ 0 := by
  intro h
  have h' := congrArg (fun v : Space => v i) h
  simp [unitVector] at h'

theorem lineGradientBound : LineGradientBound := by
  intro u hu hc i y
  have he0 : unitVector i ≠ 0 := unitVector_ne_zero i
  set e := unitVector i with he
  let φ : ℝ → Space := fun t => y + t • e
  have hφ : ContDiff ℝ 1 φ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hemb : IsClosedEmbedding φ :=
    (Homeomorph.addLeft y).isClosedEmbedding.comp (isClosedEmbedding_smul_left he0)
  have hg : ContDiff ℝ 1 (u ∘ φ) := hu.comp hφ
  have hgc : HasCompactSupport (u ∘ φ) := hc.comp_isClosedEmbedding hemb
  have hder : ∀ t, deriv (u ∘ φ) t = fderiv ℝ u (y + t • e) e := by
    intro t
    have h0 : HasDerivAt φ ((1 : ℝ) • e) t :=
      ((hasDerivAt_id t).smul_const e).const_add y
    have h1 : HasDerivAt φ e t := by
      rw [one_smul] at h0
      exact h0
    exact ((hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t h1).deriv
  have key := two_abs_le_integral_abs_deriv hg hgc 0
  simp only [hder, Function.comp_apply, φ, zero_smul, add_zero] at key
  linarith

end Breakdown
