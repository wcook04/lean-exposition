import Breakdown.CertCell.BridgeStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

theorem stripMomentTrace : StripMomentTraceHolds := by
  intro h lo hi wt t F dF hh hlo hF hdF hwt ht
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hpt : ∀ p : ℝ × ℝ, ((((1 / (0 - h) : ℝ)) : ℂ) * F p + (((p.2 - h) / (0 - h) : ℝ) : ℂ) * dF p)
      * ((wt p.1 * t p.1 : ℝ) : ℂ)
      = (dF p * ((1 - p.2 / h : ℝ) : ℂ) - F p / (h : ℂ)) * ((wt p.1 * t p.1 : ℝ) : ℂ) := by
    intro p
    push_cast
    field_simp
    ring
  have hsign : CellCert.CellFormula.edgeSign 0 h = -1 := by
    simp [CellCert.CellFormula.edgeSign, not_lt.mpr hh.le]
  have hmin : min 0 h = 0 := min_eq_left hh.le
  have hmax : max 0 h = h := max_eq_right hh.le
  have hK : IsCompact (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) h) := isCompact_Icc.prod isCompact_Icc
  have hwc : Continuous (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((hwt.mul ht).comp continuous_fst)
  have hint : IntegrableOn (fun p : ℝ × ℝ =>
      (dF p * ((1 - p.2 / h : ℝ) : ℂ) - F p / (h : ℂ)) * ((wt p.1 * t p.1 : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc 0 h) := by
    have hc : Continuous (fun p : ℝ × ℝ => ((1 - p.2 / h : ℝ) : ℂ)) := by fun_prop
    have h1 := hdF.mul_continuousOn hc.continuousOn hK
    have h2 : IntegrableOn (fun p : ℝ × ℝ => F p / (h : ℂ)) (Set.Icc lo hi ×ˢ Set.Icc 0 h) :=
      hF.div_const _
    exact (h1.sub h2).mul_continuousOn hwc.continuousOn hK
  unfold CellCert.CellFormula.heightStripMoment
  rw [hsign, hmin, hmax]
  simp_rw [hpt]
  rw [Measure.volume_eq_prod, setIntegral_prod _ (by rwa [← Measure.volume_eq_prod]),
    intervalIntegral.integral_of_le hlo.le, integral_Icc_eq_integral_Ioc, neg_one_mul, ← integral_neg]
  congr 1
  funext r
  unfold upperTrace
  simp only []
  rw [integral_mul_const, intervalIntegral.integral_of_le hh.le, integral_Icc_eq_integral_Ioc]
  ring

end Bridge

end CertCell

end Breakdown
