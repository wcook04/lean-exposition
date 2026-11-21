import Breakdown.FracCell.RelAxis
import Breakdown.FracCell.RelRadialCoef
import Breakdown.FracCell.StAngularMode

open MeasureTheory Set

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace AxisFluxInternal

theorem ae_fst_ne_zero : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  rw [Measure.volume_eq_prod]
  exact (Measure.quasiMeasurePreserving_fst).ae h

theorem hbase {R z₁ z₂ : ℝ} (hR : 0 < R) {t : ℝ → ℝ} (ht : Continuous t) (i : ℕ)
    {F D X : ℝ × ℝ → ℂ} (hF : IntegrableOn F (Icc 0 R ×ˢ Icc z₁ z₂))
    (hX : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * X p = F p)
    (hD : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 R) →
      IntegrableOn (fun p : ℝ × ℝ => ((p.1 * g p.1 * t p.2 : ℝ) : ℂ) * D p) (Icc 0 R ×ˢ Icc z₁ z₂))
    (hibp : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ 0 = 0 → ψ R = 0 →
      ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((ψ p.1 * t p.2 : ℝ) : ℂ) * D p =
        -∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((deriv ψ p.1 * t p.2 : ℝ) : ℂ) * F p) :
    ((R * R ^ i : ℝ) : ℂ) * radialStripMoment R 0 z₁ z₂ F D t
      = (∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((p.1 * (((i : ℝ) + 1) * p.1 ^ i) * t p.2 : ℝ) : ℂ) * X p)
        + ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((p.1 * p.1 ^ i * t p.2 : ℝ) : ℂ) * D p := by
  have hSm : MeasurableSet (Icc (0 : ℝ) R ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  have hSc : IsCompact (Icc (0 : ℝ) R ×ˢ Icc z₁ z₂) := isCompact_Icc.prod isCompact_Icc
  have hFg : ∀ g : ℝ → ℝ, Continuous g →
      IntegrableOn (fun p : ℝ × ℝ => ((g p.1 * t p.2 : ℝ) : ℂ) * F p) (Icc 0 R ×ˢ Icc z₁ z₂) := by
    intro g hg
    refine hF.continuousOn_mul ?_ hSc
    exact (Complex.continuous_ofReal.comp
      ((hg.comp continuous_fst).mul (ht.comp continuous_snd))).continuousOn
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hL : ((R * R ^ i : ℝ) : ℂ) * radialStripMoment R 0 z₁ z₂ F D t
      = ∫ p in Icc 0 R ×ˢ Icc z₁ z₂,
          (((R ^ i * t p.2 : ℝ) : ℂ) * F p + ((p.1 * R ^ i * t p.2 : ℝ) : ℂ) * D p) := by
    have e1 : edgeSign R 0 = 1 := by simp [edgeSign, hR]
    have e2 : min R 0 = 0 := min_eq_right hR.le
    have e3 : max R 0 = R := max_eq_left hR.le
    rw [radialStripMoment, e1, e2, e3, one_mul, ← integral_const_mul]
    refine setIntegral_congr_fun hSm (fun p _ => ?_)
    simp only [sub_zero]
    push_cast
    field_simp
  have hψd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => R ^ i * r - r ^ (i + 1))
      (R ^ i - ((i : ℝ) + 1) * r ^ i) r := by
    intro r
    have h := ((hasDerivAt_id' r).const_mul (R ^ i)).sub (hasDerivAt_pow (i + 1) r)
    exact h.congr_deriv (by rw [Nat.add_sub_cancel]; push_cast; ring)
  have hdv : deriv (fun r : ℝ => R ^ i * r - r ^ (i + 1)) = fun r => R ^ i - ((i : ℝ) + 1) * r ^ i :=
    funext fun r => (hψd r).deriv
  have hψc : ContDiff ℝ 1 (fun r : ℝ => R ^ i * r - r ^ (i + 1)) := by fun_prop
  have key := hibp _ hψc (by simp) (by ring)
  rw [hdv] at key
  have hX' : ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((p.1 * (((i : ℝ) + 1) * p.1 ^ i) * t p.2 : ℝ) : ℂ) * X p
      = ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (((((i : ℝ) + 1) * p.1 ^ i) * t p.2 : ℝ) : ℂ) * F p := by
    refine setIntegral_congr_ae hSm ?_
    filter_upwards [hX, ae_fst_ne_zero] with p hp hne hpS
    have hpos : 0 < p.1 := lt_of_le_of_ne (Set.mem_prod.1 hpS).1.1 (Ne.symm hne)
    rw [← hp hpos]
    push_cast
    ring
  rw [hL, hX', integral_add (hFg _ continuous_const) (hD _ continuousOn_const)]
  have e2 : ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (((R ^ i * p.1 - p.1 ^ (i + 1)) * t p.2 : ℝ) : ℂ) * D p
      = (∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((p.1 * R ^ i * t p.2 : ℝ) : ℂ) * D p)
        - ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((p.1 * p.1 ^ i * t p.2 : ℝ) : ℂ) * D p := by
    rw [← integral_sub (hD _ continuousOn_const) (hD (fun r => r ^ i) (continuous_pow i).continuousOn)]
    refine setIntegral_congr_fun hSm (fun p _ => ?_)
    push_cast
    ring
  have e3 : ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (((R ^ i - ((i : ℝ) + 1) * p.1 ^ i) * t p.2 : ℝ) : ℂ) * F p
      = (∫ p in Icc 0 R ×ˢ Icc z₁ z₂, ((R ^ i * t p.2 : ℝ) : ℂ) * F p)
        - ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (((((i : ℝ) + 1) * p.1 ^ i) * t p.2 : ℝ) : ℂ) * F p := by
    rw [← integral_sub (hFg _ continuous_const) (hFg (fun r => ((i : ℝ) + 1) * r ^ i) (by fun_prop))]
    refine setIntegral_congr_fun hSm (fun p _ => ?_)
    push_cast
    ring
  rw [e2, e3] at key
  linear_combination key

end AxisFluxInternal

theorem axisFlux_of (hI : AxisModeIntegrableStatement) (hRP : CellFormula.ModeRadialPartsStatement)
    (hA : AngularModeStatement) : AxisFluxStatement := by
  intro m v G H hv R z₁ z₂ hR hz t ht i σ
  have hRP' := hRP m v G hv.measurable_velocity hv.velocity_six hv.measurable_gradient hv.gradient_two
    hv.weak_gradient 0 (if σ = 0 then 0 else 1) 0 R z₁ z₂ le_rfl hR hz
  have hnz : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * (if σ = 0 then gradMode m 0 G 1 1 p else -gradMode m 0 G 0 1 p)
        = modeVec m 0 v p.1 p.2 (if σ = 0 then 0 else 1) := by
    filter_upwards [hA m v G H hv 0] with p hp hpos
    obtain ⟨h1, h2, -⟩ := hp hpos
    by_cases hσ : σ = 0
    · simp only [if_pos hσ]
      rw [h2]
      simp [azimuth]
    · simp only [if_neg hσ]
      rw [mul_neg, h1]
      simp [azimuth]
  have hFint : IntegrableOn (fun p : ℝ × ℝ => modeVec m 0 v p.1 p.2 (if σ = 0 then 0 else 1))
      (Icc 0 R ×ˢ Icc z₁ z₂) := by
    have hrX : IntegrableOn (fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (if σ = 0 then gradMode m 0 G 1 1 p else -gradMode m 0 G 0 1 p))
        (Icc 0 R ×ˢ Icc z₁ z₂) := by
      by_cases hσ : σ = 0
      · simp only [if_pos hσ]
        exact hI m v G H hv R z₁ z₂ 0 1 1
      · simp only [if_neg hσ, mul_neg]
        exact (hI m v G H hv R z₁ z₂ 0 0 1).neg
    refine hrX.congr_fun_ae ?_
    refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 ?_
    filter_upwards [hnz, AxisFluxInternal.ae_fst_ne_zero] with p hp hne hpS
    exact hp (lt_of_le_of_ne (Set.mem_prod.1 hpS).1.1 (Ne.symm hne))
  exact AxisFluxInternal.hbase hR ht i hFint hnz (fun g hg => hRP'.1 g t hg ht)
    (fun ψ hψ h0 hR' => hRP'.2 ψ t hψ ht h0 hR')

end Breakdown.CellCert.CellFormula
