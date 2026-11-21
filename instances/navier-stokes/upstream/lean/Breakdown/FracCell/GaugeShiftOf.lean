import Breakdown.FracCell.FormulaDataDefs

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace GaugeShiftOf.Internal

variable (L : CellLayout)

theorem negMode_zero (n : L.modes) (h : (n : ℤ) = 0) : L.negMode n = n := by
  unfold CellLayout.negMode
  have hm : -(n : ℤ) ∈ L.modes := by rw [h, neg_zero, ← h]; exact n.2
  rw [dif_pos hm]
  exact Subtype.ext (by simp [h])

theorem shift_eq {k : ℕ} (left right : FieldTuple k → ℝ) (x : FieldTuple k)
    (n : L.modes) (s : Fin L.presCount) (j : Fin L.degSide) (h0 : (n : ℤ) = 0) :
    L.pressureShift (L.gaugeShiftOf left right) x (CellDatum.sidePressure n s j) =
      ((L.shiftCoefLeft (s, j) * left x + L.shiftCoefRight (s, j) * right x : ℝ) : ℂ) := by
  simp only [CellLayout.pressureShift, CellDatum.sidePressure, Sum.elim_inl, Sum.elim_inr, if_pos h0]
  simp only [CellLayout.shiftCoefLeft, CellLayout.shiftCoefRight, CellLayout.gaugeShiftOf]
  split_ifs <;> push_cast <;> ring

theorem pdv_eq {k : ℕ} (hz : (0 : ℤ) ∈ L.modes) (x : FieldTuple k) (s : Fin L.presCount) (j : Fin L.degSide) :
    L.pressureDatumValue x (s, j) = (L.trueData x (CellDatum.sidePressure ⟨0, hz⟩ s j)).re := by
  simp only [CellLayout.pressureDatumValue, CellLayout.zeroMode, dif_pos hz]

theorem true_real (hc : ConjugateDataStatement) {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} (hL : IsPressureLayout c K S B L) {x : FieldTuple k} (hx : IsAdmissible c x)
    (n : L.modes) (h : (n : ℤ) = 0) (s : Fin L.presCount) (j : Fin L.degSide) :
    L.trueData x (CellDatum.sidePressure n s j) = ((L.trueData x (CellDatum.sidePressure n s j)).re : ℂ) := by
  have hcj := hc c K S B L hL x hx (CellDatum.sidePressure n s j)
  have hd : L.conjDatum (CellDatum.sidePressure n s j) = CellDatum.sidePressure n s j := by
    simp only [CellLayout.conjDatum, CellDatum.sidePressure, Sum.map_inr, Sum.map_inl, negMode_zero L n h]
  rw [hd] at hcj
  exact (Complex.conj_eq_iff_re.mp hcj.symm).symm

end GaugeShiftOf.Internal

open GaugeShiftOf.Internal in
theorem gaugeShiftOf_of (hc : ConjugateDataStatement) : GaugeShiftOfStatement := by
  intro k N c K S B L sp hL hsp left right hlin hedge hroot
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y a b hx hy
    obtain ⟨h1, h2⟩ := hlin x y a b hx hy
    refine ⟨h1, h2, fun r => ?_⟩
    simp only [CellLayout.gaugeShiftOf]
    split_ifs
    · exact h2
    · exact h1
  · intro _ x
    simp only [CellLayout.gaugeShiftOf, if_neg hsp.box_ne]
  · intro x
    simp only [CellLayout.gaugeShiftOf, if_true]
  · intro x hx d hd
    rcases d with i | i | i | i | ⟨n, s, j⟩ | i | i | i <;>
      simp only [CellLayout.IsGaugeDeleted, Sum.elim_inl, Sum.elim_inr] at hd
    obtain ⟨hn0, hmem⟩ := hd
    have hn : n = ⟨0, hsp.zero_mode⟩ := Subtype.ext hn0
    subst hn
    have hshift := shift_eq L left right x ⟨0, hsp.zero_mode⟩ s j rfl
    have hreal := true_real L hc hL hx ⟨0, hsp.zero_mode⟩ rfl s j
    have hpdv := pdv_eq L hsp.zero_mode x s j
    change L.trueData x (CellDatum.sidePressure _ s j) +
      L.pressureShift (L.gaugeShiftOf left right) x (CellDatum.sidePressure _ s j) = 0
    rw [hshift, hreal, ← hpdv, ← Complex.ofReal_add, Complex.ofReal_eq_zero]
    rcases (hsp.deleted_eq (s, j)).mp hmem with he | hr
    · have hb := hsp.edge_balanced _ he
      have hne := hsp.edge_right_ne _ he
      have hj := hedge _ he x hx
      have hg : L.gaugeJump sp x = -(L.pressureDatumValue x (s, j)) / L.shiftCoefRight (s, j) := by
        simp only [CellLayout.gaugeJump, he]
      have hl : L.shiftCoefLeft (s, j) = -L.shiftCoefRight (s, j) := by linarith
      rw [hj, hg, hl]
      field_simp
      ring
    · have hz := hroot _ hr x hx
      unfold CellLayout.rootShifted at hz
      linarith

end Breakdown.CellCert.CellFormula
