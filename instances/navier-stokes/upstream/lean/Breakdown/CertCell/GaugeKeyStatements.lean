import Breakdown.CertCell.TopStatements
import Breakdown.CertCell.GaugeKeyValues
import Breakdown.CertCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace GaugeKey

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def fieldHyp (D : CellLayerData k C nE nM) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g Pg : ℝ → Space → Space) : Prop :=
  q ∈ D.cert.params ∧ Bridge.IsModeClass D.cert.symmetries D.azimuthOrder ∧
    IsPerturbation D.cert.symmetries (D.cert.period q) v G H g ∧
    CellCalculus.IsPeriodicPressure Pg ∧ ∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)

end GaugeKey

namespace TreeEntry

open CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculus.CellCalculusEntry D}
  (T : TreeEntry D R)

def keyState {q : Fin k → ℝ} (x : AdmissibleTuple D D.coercivity q) (ι : ℤ × ℤ) (key : SkeletonKey) : ℂ :=
  keyHarmonic T.keyLayout (labelTime ι) x.v x.G x.H (chosenPressure D x) key
    + ∑ c, T.gaugeValue c q x * T.gauge.dir c ι key

def KeyPartCovered (ι : ℤ × ℤ) (key : SkeletonKey) (imag : Bool) : Prop :=
  (∃ a, T.skelKey a = some (ι, key) ∧ T.evalImag a = imag) ∨ T.KeyPartOmitted ι key imag

def GaugeConjHolds : Prop :=
  ∀ q ∈ D.cert.params, ∀ (x : AdmissibleTuple D D.coercivity q) (c : Fin T.gauge.count),
    T.gaugeValue (T.gauge.conjClass c) q x = (starRingEnd ℂ) (T.gaugeValue c q x)

def DeletedPartZero : Prop :=
  ∀ q ∈ D.cert.params, ∀ (x : AdmissibleTuple D D.coercivity q) (e : Fin T.gauge.count),
    T.keyState x (T.gauge.deletedKey e).1 (T.gauge.deletedKey e).2 = 0

theorem labelTime_neg (ι : ℤ × ℤ) : labelTime (-ι) = -labelTime ι := by
  simp only [labelTime, Prod.fst_neg, Prod.snd_neg]; ring

theorem gaugeValue_eq {q : Fin k → ℝ} (x : AdmissibleTuple D D.coercivity q) (c : Fin T.gauge.count) :
    T.gaugeValue c q x = T.gauge.shiftValue (fun e => keyHarmonic T.keyLayout (labelTime (T.gauge.deletedKey e).1)
      x.v x.G x.H (chosenPressure D x) (T.gauge.deletedKey e).2) c := rfl

theorem deletedPartZero_of (hG : T.gauge.Conditions) : T.DeletedPartZero := by
  intro q _ x e
  simp only [keyState, T.gaugeValue_eq x]
  exact T.gauge.deleted_shift_zero hG (fun e' => keyHarmonic T.keyLayout (labelTime (T.gauge.deletedKey e').1)
    x.v x.G x.H (chosenPressure D x) (T.gauge.deletedKey e').2) e

def FieldKeyConjHolds : Prop :=
  ∀ (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (key : SkeletonKey),
    GaugeKey.keyMode key = some 0 →
      keyHarmonic T.keyLayout (-ν) v G H Pg key = (starRingEnd ℂ) (keyHarmonic T.keyLayout ν v G H Pg key)

def FieldRealLabelZero : Prop :=
  ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (key : SkeletonKey),
    GaugeKey.keyMode key = some 0 → (keyHarmonic T.keyLayout 0 v G H Pg key).im = 0

def FieldPlanePairZero : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (ι : ℤ × ℤ) (key : SkeletonKey) (imag : Bool),
      GaugeKey.PlanePairOmitted ι key imag → GaugeKey.KeyInHalfPlane key → GaugeKey.keyPart imag (keyHarmonic T.keyLayout (labelTime ι) v G H Pg key) = 0

def FieldPlaneOddZero : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (ι : ℤ × ℤ) (key : SkeletonKey),
      GaugeKey.PlaneOddOmitted ι key → GaugeKey.KeyInHalfPlane key → keyHarmonic T.keyLayout (labelTime ι) v G H Pg key = 0

def FieldGaugeConj : Prop :=
  ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (c : Fin T.gauge.count),
    T.fieldGauge (T.gauge.conjClass c) v G H Pg = (starRingEnd ℂ) (T.fieldGauge c v G H Pg)

def FieldDeletedZero : Prop :=
  ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (e : Fin T.gauge.count),
    T.fieldKey v G H Pg (T.gauge.deletedKey e).1 (T.gauge.deletedKey e).2 = 0

def FieldKeyPartZero : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (ι : ℤ × ℤ) (key : SkeletonKey) (imag : Bool),
      T.KeyPartOmitted ι key imag → GaugeKey.keyPart imag (T.fieldKey v G H Pg ι key) = 0

structure FieldGaugeHolds : Prop where
  conj : T.FieldGaugeConj
  deleted : T.FieldDeletedZero
  omitted : T.FieldKeyPartZero

theorem fieldGauge_eq (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (c : Fin T.gauge.count) :
    T.fieldGauge c v G H Pg = T.gauge.shiftValue (fun e => keyHarmonic T.keyLayout (labelTime (T.gauge.deletedKey e).1)
      v G H Pg (T.gauge.deletedKey e).2) c := rfl

theorem fieldDeletedZero_of (hG : T.gauge.Conditions) : T.FieldDeletedZero := by
  intro v G H Pg e
  simp only [fieldKey, T.fieldGauge_eq]
  exact T.gauge.deleted_shift_zero hG (fun e' => keyHarmonic T.keyLayout (labelTime (T.gauge.deletedKey e').1)
    v G H Pg (T.gauge.deletedKey e').2) e

theorem fieldGaugeConj_of (hG : T.gauge.Conditions) (hK : T.FieldKeyConjHolds) : T.FieldGaugeConj := by
  intro v G H Pg c
  rw [T.fieldGauge_eq, T.fieldGauge_eq]
  apply T.gauge.shift_conj hG
  intro e
  obtain ⟨rad, lev, lo, hi, t, d, hd⟩ := hG.deleted_pressure e
  have hl : (T.gauge.deletedKey (T.gauge.conjClass e)).1 = -(T.gauge.deletedKey e).1 := by
    rw [hG.deleted_label, hG.deleted_label, hG.conj_label]
  simp only [hl, hG.deleted_conj, labelTime_neg]
  apply hK
  rw [hd]; rfl

theorem fieldKeyPartZero_of (hG : T.gauge.Conditions) (hc : T.FieldGaugeConj) (h0 : T.FieldRealLabelZero)
    (h1 : T.FieldPlanePairZero) (h2 : T.FieldPlaneOddZero) : T.FieldKeyPartZero := by
  intro q v G H g Pg hyp ι key imag h
  rcases h with h | ⟨h, hgeo⟩ | ⟨h, hgeo⟩ | ⟨e, he⟩
  · obtain ⟨rfl, hm, rfl⟩ := h
    have hlt : labelTime (0 : ℤ × ℤ) = 0 := by simp [labelTime]
    simp only [GaugeKey.keyPart, if_true, fieldKey, Complex.add_im, Complex.im_sum, hlt]
    rw [h0 v G H Pg key hm, zero_add]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hd : T.gauge.dir c 0 key = 0
    · simp [hd]
    · obtain ⟨hl, -⟩ := T.gauge.dir_support hd
      have hself := hG.conj_self c hl.symm
      have hre : (T.fieldGauge c v G H Pg).im = 0 := by
        have := hc v G H Pg c
        rw [hself] at this
        exact Complex.conj_eq_iff_im.mp this.symm
      simp only [GaugeKey.GaugeKeyValues.dir, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hre]
      ring
  · have hz : ∀ c, T.gauge.dir c ι key = 0 := by
      intro c
      by_contra hd
      obtain ⟨hl, -⟩ := T.gauge.dir_support hd
      have ha := hG.label_axis c
      rw [← hl] at ha
      obtain ⟨h1', h2', -⟩ := h
      omega
    simp only [fieldKey, hz, mul_zero, Finset.sum_const_zero, add_zero]
    exact h1 q v G H g Pg hyp ι key imag h hgeo
  · have hz : ∀ c, T.gauge.dir c ι key = 0 := by
      intro c
      by_contra hd
      obtain ⟨-, rad, lev, lo, hi, t, d, rfl⟩ := T.gauge.dir_support hd
      obtain ⟨-, -, hs⟩ := h
      simp only [GaugeKey.planeSign] at hs
      split_ifs at hs <;> simp at hs <;> norm_num at hs
    simp only [fieldKey, hz, mul_zero, Finset.sum_const_zero, add_zero, h2 q v G H g Pg hyp ι key h hgeo]
    cases imag <;> simp [GaugeKey.keyPart]
  · have hz := T.fieldDeletedZero_of hG v G H Pg e
    rw [he] at hz
    simp [hz, GaugeKey.keyPart]

theorem fieldGaugeHolds_of (hG : T.gauge.Conditions) (hK : T.FieldKeyConjHolds) (h0 : T.FieldRealLabelZero)
    (h1 : T.FieldPlanePairZero) (h2 : T.FieldPlaneOddZero) : T.FieldGaugeHolds :=
  ⟨T.fieldGaugeConj_of hG hK, T.fieldDeletedZero_of hG,
    T.fieldKeyPartZero_of hG (T.fieldGaugeConj_of hG hK) h0 h1 h2⟩

theorem gaugeConj_of (hG : T.gauge.Conditions) (hK : T.FieldKeyConjHolds) : T.GaugeConjHolds :=
  fun _ _ x c => T.fieldGaugeConj_of hG hK x.v x.G x.H (chosenPressure D x) c

end TreeEntry

end CertCell

end Breakdown
