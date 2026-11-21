import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.GaugeKeyConj

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

namespace Internal.DatumConj

theorem coef_negField (B : CellBases) (K : CellBox) (F : ℝ × ℝ → ℂ) (j l : ℕ) :
    B.coef K (-F) j l = -B.coef K F j l := by
  unfold CellBases.coef
  rw [← integral_neg]
  congr 1
  funext p
  simp only [Pi.neg_apply]
  ring

theorem extraValue_negField (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (n : ℤ) (e : Fin 4)
    (a : Fin 3) (d : ℕ) : L.extraValue n (-x) e a d = -L.extraValue n x e a d := by
  unfold CellLayout.extraValue
  simp only [KeyConjInternal.velMode_negField, KeyConjInternal.gradModeOf_negField,
    KeyConjInternal.radialStripMoment_negField, KeyConjInternal.heightStripMoment_negField]
  split_ifs <;> rfl

theorem headData_negField (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (d : L.Datum) :
    headData L (-x) d = -headData L x d := by
  rcases d with i | i | i | i | i | i | c | i
  · show L.trueData (-x) (Sum.inl i) = -L.trueData x (Sum.inl i)
    simp only [CellLayout.trueData, Sum.elim_inl, KeyConjInternal.gradModeOf_negField, coef_negField]
  · show L.trueData (-x) (Sum.inr (Sum.inl i)) = -L.trueData x (Sum.inr (Sum.inl i))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, KeyConjInternal.velMode_negField, coef_negField]
  · show L.trueData (-x) (Sum.inr (Sum.inr (Sum.inl i))) = -L.trueData x (Sum.inr (Sum.inr (Sum.inl i)))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, KeyConjInternal.velMode_negField,
      KeyConjInternal.gradModeOf_negField, KeyConjInternal.moment_negField]
  · show L.trueData (-x) (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      = -L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, KeyConjInternal.gradModeOf_negField,
      KeyConjInternal.secondModeOf_negField, KeyConjInternal.moment_negField]
    split_ifs <;> rfl
  · simp only [headData]
    rw [KeyConjInternal.moment_congr_ae _ _ (KeyConjInternal.headPressure_negField L x i.1),
      KeyConjInternal.pressureGradMode_negField, KeyConjInternal.pressureGradMode_negField,
      KeyConjInternal.moment_negField]
  · show L.trueData (-x) (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
      = -L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, KeyConjInternal.velMode_negField,
      KeyConjInternal.gradModeOf_negField, KeyConjInternal.secondModeOf_negField,
      KeyConjInternal.cornerMoment_negField]
  · show L.trueData (-x) (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))))))
      = -L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))))))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, KeyConjInternal.velMode_negField,
      KeyConjInternal.gradModeOf_negField, KeyConjInternal.heightStripMoment_negField]
  · show L.trueData (-x) (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))))
      = -L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))))
    simp only [CellLayout.trueData, Sum.elim_inr, extraValue_negField]

theorem headData_zeroField (L : CellLayout) {j : ℕ} (d : L.Datum) :
    headData L (0 : CellCert.Assembly.FieldTuple j) d = 0 := by
  have h := headData_negField L (0 : CellCert.Assembly.FieldTuple j) d
  rw [neg_zero] at h
  linear_combination h / 2

end Internal.DatumConj

namespace Internal.DatumConj

theorem presMode_negMode (m : ℕ) (n : ℤ) (P : Space → ℝ) (r z : ℝ) :
    presMode m (-n) P r z = conj (presMode m n P r z) := by
  unfold presMode
  rw [ConjugateDataInternal.conj_angle]

theorem headData_conj (L L' : CellLayout) (hord : L'.order = L.order) {j : ℕ} (x : CellCert.Assembly.FieldTuple j)
    (d : L.Datum) (d' : L'.Datum) (h : ConjDatum L L' d d') : headData L' x d' = conj (headData L x d) := by
  have hv : ∀ n a, L'.velMode n x a = L.velMode n x a := fun n a => by
    funext p; simp only [CellLayout.velMode, hord]
  have hg : ∀ n a b, L'.gradModeOf n x a b = L.gradModeOf n x a b := fun n a b => by
    simp only [CellLayout.gradModeOf, hord]
  have hs : ∀ n a b c, L'.secondModeOf n x a b c = L.secondModeOf n x a b c := fun n a b c => by
    simp only [CellLayout.secondModeOf, hord]
  have hp : ∀ n a, L'.pressureGradMode n x a = L.pressureGradMode n x a := fun n a => by
    funext p; simp only [CellLayout.pressureGradMode, hord]
  have hh : ∀ n, headPressure L' n x = headPressure L n x := fun n => by
    funext p; simp only [headPressure, hord]
  rcases d with i | i | i | i | i | i | c | i <;> rcases d' with i' | i' | i' | i' | i' | i' | c' | i' <;>
    simp only [ConjDatum] at h
  · obtain ⟨hK, hB, hn, ha, hb, hj, hl⟩ := h
    show L'.trueData x (Sum.inl i') = conj (L.trueData x (Sum.inl i))
    simp only [CellLayout.trueData, Sum.elim_inl]
    rw [ConjugateDataInternal.conj_coef, ← ConjugateDataInternal.gradModeOf_neg, hg, hn, hK, hB, ha, hb, hj, hl]
  · obtain ⟨hK, hB, hn, ha, hj, hl⟩ := h
    show L'.trueData x (Sum.inr (Sum.inl i')) = conj (L.trueData x (Sum.inr (Sum.inl i)))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [ConjugateDataInternal.conj_coef, ← ConjugateDataInternal.velMode_neg, hv, hn, hK, hB, ha, hj, hl]
  · obtain ⟨hn, hS, ha, hj⟩ := h
    show L'.trueData x (Sum.inr (Sum.inr (Sum.inl i'))) = conj (L.trueData x (Sum.inr (Sum.inr (Sum.inl i))))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [ConjugateDataInternal.conj_segMoment, ← ConjugateDataInternal.velMode_neg,
      ← ConjugateDataInternal.gradModeOf_neg, ← ConjugateDataInternal.gradModeOf_neg, hv, hg, hg, hn, hS, ha, hj]
  · obtain ⟨hn, hS, ha, hj⟩ := h
    show L'.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))))
      = conj (L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [hS, ha, hj]
    split_ifs <;>
      rw [ConjugateDataInternal.conj_segMoment, ← ConjugateDataInternal.gradModeOf_neg,
        ← ConjugateDataInternal.secondModeOf_neg, ← ConjugateDataInternal.secondModeOf_neg, hg, hs, hs, hn]
  · obtain ⟨hn, hS, hj⟩ := h
    simp only [headData]
    rw [ConjugateDataInternal.conj_segMoment, ← ConjugateDataInternal.pressureGradMode_neg,
      ← ConjugateDataInternal.pressureGradMode_neg, hp, hp, hh, hn, hS, hj]
    congr 1
    funext p
    simp only [headPressure, presMode_negMode]
  · obtain ⟨hn, hc, ho, ha⟩ := h
    show L'.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i'))))))
      = conj (L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [ConjugateDataInternal.conj_corner, ← ConjugateDataInternal.velMode_neg,
      ← ConjugateDataInternal.gradModeOf_neg, ← ConjugateDataInternal.gradModeOf_neg,
      ← ConjugateDataInternal.secondModeOf_neg, hv, hg, hg, hs, hn, hc, ho, ha]
  · obtain ⟨hc, ho⟩ := h
    show L'.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c')))))))
      = conj (L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c))))))))
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [ConjugateDataInternal.conj_heightStrip, ← ConjugateDataInternal.velMode_neg,
      ← ConjugateDataInternal.gradModeOf_neg, neg_zero, hv, hg, hc, ho]
  · obtain ⟨hK, hB, hn, he, ha, hj⟩ := h
    show L'.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i')))))))
      = conj (L.trueData x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))))))
    simp only [CellLayout.trueData, Sum.elim_inr]
    rw [← ConjugateDataInternal.extraValue_neg, ← hn, ← he, ← ha, ← hj]
    unfold CellLayout.extraValue CellLayout.sideTest
    simp only [hv, hg, hK, hB]

end Internal.DatumConj

namespace Internal.DatumConj

theorem headHarmonic_negLabel (L L' : CellLayout) (hord : L'.order = L.order) (ν : ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (d : L.Datum) (d' : L'.Datum) (h : ConjDatum L L' d d') :
    headHarmonic L' (-ν) v G H Pg d' = conj (headHarmonic L ν v G H Pg d) := by
  unfold headHarmonic
  rw [KeyConjInternal.cosTuple_negFreq, KeyConjInternal.sinTuple_negFreq, headData_negField,
    headData_conj L L' hord _ d d' h, headData_conj L L' hord _ d d' h, map_add, map_mul, Complex.conj_I]
  ring

theorem conjDatum_self (L : CellLayout) (hm : ∀ n ∈ L.modes, n = 0) (d : L.Datum) : ConjDatum L L d d := by
  rcases d with i | i | i | i | i | i | c | i <;>
    first | (simp [ConjDatum]; done) | simp [ConjDatum, hm _ i.1.2]

theorem headHarmonic_zero_im (L : CellLayout) (hm : ∀ n ∈ L.modes, n = 0) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (d : L.Datum) : (headHarmonic L 0 v G H Pg d).im = 0 := by
  have h := headHarmonic_negLabel L L rfl 0 v G H Pg d d (conjDatum_self L hm d)
  rw [neg_zero] at h
  exact Complex.conj_eq_iff_im.mp h.symm

theorem dir_keyOf_conj (Γ : GaugeKey.GaugeKeyValues) (c : Fin Γ.count) (ι : ℤ × ℤ) (L L' : CellLayout)
    (d : L.Datum) (d' : L'.Datum) (h : ConjDatum L L' d d') : Γ.dir c ι (keyOf L' d') = Γ.dir c ι (keyOf L d) := by
  rcases d with i | i | i | i | i | i | c | i <;> rcases d' with i' | i' | i' | i' | i' | i' | c' | i' <;>
    simp only [ConjDatum] at h <;>
    try simp [keyOf, GaugeKey.GaugeKeyValues.dir, GaugeKey.GaugeKeyValues.dirReal]
  obtain ⟨hn, hS, hj⟩ := h
  rw [hn, ← hS, ← hj]
  by_cases hz : (i.1 : ℤ) = 0
  · rw [hz, neg_zero]
  · have hz' : -(i.1 : ℤ) ≠ 0 := neg_ne_zero.mpr hz
    simp [hz, hz']

theorem keyOf_conj_of_modeZero (L L' : CellLayout) (d : L.Datum) (d' : L'.Datum) (h : ConjDatum L L' d d')
    (hk : ∃ rad lev lo hi t dd, keyOf L d = SkeletonKey.pressure 0 rad lev lo hi t dd) : keyOf L' d' = keyOf L d := by
  obtain ⟨rad, lev, lo, hi, t, dd, hk⟩ := hk
  rcases d with i | i | i | i | i | i | c | i <;> rcases d' with i' | i' | i' | i' | i' | i' | c' | i' <;>
    simp only [ConjDatum] at h <;> simp only [keyOf, Sum.elim_inl, Sum.elim_inr] at hk ⊢ <;>
    try (simp at hk; done)
  obtain ⟨hn, hS, hj⟩ := h
  have h0 : (i.1 : ℤ) = 0 := (SkeletonKey.pressure.inj hk).1
  rw [hn, ← hS, ← hj, h0, neg_zero]

end Internal.DatumConj

end Assembly

end CertCell

end Breakdown
