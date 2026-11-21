import Breakdown.FracCell.StMesh
import Breakdown.FracCell.MeshGaugeLinearPotential
import Breakdown.FracCell.MeshGaugeLinearMoment

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

namespace MeshGaugeLinearParts

open SteadyCert Assembly CellAnalysis CellFormula

private theorem vol_rect (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    (volume : Measure (ℝ × ℝ)).real (Set.Icc a b ×ˢ Set.Icc c d) = (b - a) * (d - c) := by
  rw [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith), ENNReal.toReal_ofReal (by nlinarith)]

private theorem test_zero (S : FaceSegment) (s : ℝ) : S.test 0 s = S.testCoef 0 0 := by
  simp [FaceSegment.test]

private theorem edgeSign_ne (c o : ℝ) : edgeSign c o ≠ 0 := by
  unfold edgeSign
  split_ifs <;> norm_num

theorem gaugeUnit_ne (L : CellLayout) (hgauge : IsFaceSegment L.gauge ∧ L.gauge.testCoef 0 0 ≠ 0 ∧ 0 ≤ L.gauge.lo) :
    L.gaugeUnit ≠ 0 := by
  obtain ⟨hS, ht, hlo⟩ := hgauge
  have hco : L.gauge.level - L.gauge.other ≠ 0 := sub_ne_zero.mpr (Ne.symm hS.other_ne)
  have hmm : min L.gauge.level L.gauge.other < max L.gauge.level L.gauge.other :=
    min_lt_max.mpr (Ne.symm hS.other_ne)
  have hlh := hS.lo_lt_hi
  unfold CellLayout.gaugeUnit FaceSegment.moment
  split_ifs with hr h1
  · unfold radialStripMoment
    have hf : (fun p : ℝ × ℝ => ((((1 / (L.gauge.level - L.gauge.other) : ℝ)) : ℂ) * (fun _ => (1 : ℂ)) p +
        (((p.1 - L.gauge.other) / (L.gauge.level - L.gauge.other) : ℝ) : ℂ) * (fun _ => (0 : ℂ)) p) *
        ((L.gauge.test 0 p.2 : ℝ) : ℂ)) =
        fun _ => (((1 / (L.gauge.level - L.gauge.other)) * L.gauge.testCoef 0 0 : ℝ) : ℂ) := by
      funext p
      simp [test_zero]
    rw [hf, setIntegral_const, vol_rect _ _ _ _ hmm.le hlh.le]
    refine mul_ne_zero (edgeSign_ne _ _) ?_
    rw [Complex.real_smul]
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast mul_ne_zero (sub_ne_zero.mpr hmm.ne') (sub_ne_zero.mpr hlh.ne')
    · exact_mod_cast mul_ne_zero (one_div_ne_zero hco) ht
  · unfold heightStripMoment
    have hf : (fun p : ℝ × ℝ => ((((1 / (L.gauge.level - L.gauge.other) : ℝ)) : ℂ) * (fun _ => (1 : ℂ)) p +
        (((p.2 - L.gauge.other) / (L.gauge.level - L.gauge.other) : ℝ) : ℂ) * (fun _ => (0 : ℂ)) p) *
        ((((fun r => r) p.1) * L.gauge.test 0 p.1 : ℝ) : ℂ)) =
        fun p => ((((1 / (L.gauge.level - L.gauge.other)) * L.gauge.testCoef 0 0) * p.1 * 1 : ℝ) : ℂ) := by
      funext p
      simp [test_zero]
      ring
    rw [hf, integral_complex_ofReal, Measure.volume_eq_prod,
      setIntegral_prod_mul (fun r : ℝ => (1 / (L.gauge.level - L.gauge.other)) * L.gauge.testCoef 0 0 * r)
        (fun _ : ℝ => (1 : ℝ)), setIntegral_const, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hlh.le, integral_id]
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    refine mul_ne_zero (edgeSign_ne _ _) ?_
    have h2 : L.gauge.hi ^ 2 - L.gauge.lo ^ 2 ≠ 0 := by nlinarith
    have h3 : max L.gauge.level L.gauge.other - min L.gauge.level L.gauge.other ≠ 0 := sub_ne_zero.mpr hmm.ne'
    exact_mod_cast (by simp [h2, h3, hco, ht] :
      (1 / (L.gauge.level - L.gauge.other) * L.gauge.testCoef 0 0 * ((L.gauge.hi ^ 2 - L.gauge.lo ^ 2) / 2)) *
        ((max L.gauge.level L.gauge.other - min L.gauge.level L.gauge.other) • (1 : ℝ)) ≠ 0)
  · exact absurd rfl h1


theorem pressureDatum_linear {k N : ℕ} {c : FracCellData k N} (L : CellLayout) (hmode : (0 : ℤ) ∈ L.modes)
    (hgauge : IsFaceSegment L.gauge ∧ L.gauge.testCoef 0 0 ≠ 0 ∧ 0 ≤ L.gauge.lo ∧
      (L.gauge.radial → L.gauge.level ≠ 0 ∧ 0 ≤ min L.gauge.level L.gauge.other))
    (hseg : ∀ s, IsFaceSegment (L.presSegment s))
    (hrad : ∀ s, (L.presSegment s).radial →
      (L.presSegment s).level ≠ 0 ∧ 0 ≤ min (L.presSegment s).level (L.presSegment s).other)
    (i : Fin L.presCount × Fin L.degSide) (x y : FieldTuple k) (a b : ℝ)
    (hx : IsAdmissible c x) (hy : IsAdmissible c y) :
    L.pressureDatumValue (a • x + b • y) i = a * L.pressureDatumValue x i + b * L.pressureDatumValue y i := by
  have hQx : IsGradientField x.2.2.2.2 := hx.2.1
  have hQy : IsGradientField y.2.2.2.2 := hy.2.1
  obtain ⟨C, hC⟩ := MeshGaugeLinearPotential.potential_affine x.2.2.2.2 y.2.2.2.2 hQx hQy a b
  have hgu : L.gaugeUnit ≠ 0 := gaugeUnit_ne L ⟨hgauge.1, hgauge.2.1, hgauge.2.2.1⟩
  have hQz : (a • x + b • y).2.2.2.2 = a • x.2.2.2.2 + b • y.2.2.2.2 := rfl
  have hgv : ∀ z : FieldTuple k, L.gaugeValue z = L.gauge.moment true
      (fun p => presMode L.order 0 (fun w => potentialOf z.2.2.2.2 w - 0) p.1 p.2)
      (fun p => modeVec L.order 0 z.2.2.2.2 p.1 p.2 0) (fun p => modeVec L.order 0 z.2.2.2.2 p.1 p.2 2) 0 := by
    intro z
    simp only [sub_zero]
    rfl
  have hG := MeshGaugeLinearMoment.presMoment_affine L.gauge hgauge.1 hgauge.2.2.2 L.order x.2.2.2.2 y.2.2.2.2 hQx hQy a b C 0 0 0 hC 0
  rw [← hQz, ← hgv, ← hgv, ← hgv] at hG
  have hunit : L.gauge.moment true (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 = L.gaugeUnit := rfl
  rw [hunit] at hG
  have he : (L.gaugeValue (a • x + b • y) / L.gaugeUnit).re =
      a * (L.gaugeValue x / L.gaugeUnit).re + b * (L.gaugeValue y / L.gaugeUnit).re + C := by
    rw [hG]
    have : ((a : ℂ) * L.gaugeValue x + (b : ℂ) * L.gaugeValue y +
        ((C - 0 + a * 0 + b * 0 : ℝ) : ℂ) * L.gaugeUnit) / L.gaugeUnit =
        (a : ℂ) * (L.gaugeValue x / L.gaugeUnit) + (b : ℂ) * (L.gaugeValue y / L.gaugeUnit) + (C : ℂ) := by
      field_simp
      push_cast
      ring
    rw [this]
    simp [Complex.add_re]
  have hz : L.zeroMode = some ⟨0, hmode⟩ := by
    simp [CellLayout.zeroMode, hmode]
  have hdat : ∀ z : FieldTuple k, L.pressureDatumValue z i = ((L.presSegment i.1).moment true
      (fun p => presMode L.order 0 (fun w => potentialOf z.2.2.2.2 w - (L.gaugeValue z / L.gaugeUnit).re) p.1 p.2)
      (fun p => modeVec L.order 0 z.2.2.2.2 p.1 p.2 0) (fun p => modeVec L.order 0 z.2.2.2.2 p.1 p.2 2) i.2).re := by
    intro z
    unfold CellLayout.pressureDatumValue
    rw [hz]
    rfl
  rw [hdat, hdat, hdat]
  have hP := MeshGaugeLinearMoment.presMoment_affine (L.presSegment i.1) (hseg i.1) (hrad i.1) L.order x.2.2.2.2 y.2.2.2.2 hQx hQy a b C
    (L.gaugeValue x / L.gaugeUnit).re (L.gaugeValue y / L.gaugeUnit).re
    (L.gaugeValue (a • x + b • y) / L.gaugeUnit).re hC i.2
  rw [← hQz] at hP
  rw [hP, he]
  have h0 : (C - (a * (L.gaugeValue x / L.gaugeUnit).re + b * (L.gaugeValue y / L.gaugeUnit).re + C) +
      a * (L.gaugeValue x / L.gaugeUnit).re + b * (L.gaugeValue y / L.gaugeUnit).re : ℝ) = 0 := by ring
  rw [h0]
  simp [Complex.add_re]

end MeshGaugeLinearParts

end CellCoordinates

end CellCert

end Breakdown
