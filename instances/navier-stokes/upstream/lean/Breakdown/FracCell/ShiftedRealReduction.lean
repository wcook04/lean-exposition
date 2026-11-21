import Breakdown.FracCell.FormulaDataDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace ShiftedRealReduction.Internal

variable (L : CellLayout)

theorem negMode_val (hs : ∀ n ∈ L.modes, -n ∈ L.modes) (n : L.modes) : (L.negMode n).1 = -n.1 := by
  unfold CellLayout.negMode
  rw [dif_pos (hs _ n.2)]

theorem negMode_of_zero (n : L.modes) (h : n.1 = 0) : L.negMode n = n := by
  unfold CellLayout.negMode
  have hm : -n.1 ∈ L.modes := by rw [h, neg_zero, ← h]; exact n.2
  rw [dif_pos hm]
  exact Subtype.ext (by simp [h])

theorem modeOf_conj (hs : ∀ n ∈ L.modes, -n ∈ L.modes) (d : L.Datum) :
    L.modeOf (L.conjDatum d) = -L.modeOf d := by
  rcases d with i | i | i | i | i | i | i | i <;>
    simp [CellLayout.modeOf, CellLayout.conjDatum, negMode_val L hs]

theorem conj_of_modeOf_zero (d : L.Datum) (h : L.modeOf d = 0) : L.conjDatum d = d := by
  rcases d with i | i | i | i | i | i | i | i <;>
    simp only [CellLayout.modeOf, CellLayout.conjDatum, Sum.elim_inl, Sum.elim_inr, Sum.map_inl,
      Sum.map_inr, id] at h ⊢
  all_goals first
    | rfl
    | rw [negMode_of_zero L _ h]

theorem plane_conj (d : L.Datum) : L.IsPlaneDeleted (L.conjDatum d) ↔ L.IsPlaneDeleted d := by
  rcases d with i | i | i | i | i | i | i | i <;>
    simp [CellLayout.IsPlaneDeleted, CellLayout.conjDatum]

theorem modeOf_of_gauge (d : L.Datum) (h : L.IsGaugeDeleted d) : L.modeOf d = 0 := by
  rcases d with i | i | i | i | i | i | i | i <;>
    simp [CellLayout.IsGaugeDeleted, CellLayout.modeOf] at h ⊢
  exact h.1

theorem shift_im {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) (d : L.Datum) :
    (L.pressureShift g x d).im = 0 := by
  rcases d with i | i | i | i | i | i | i | i <;>
    simp only [CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr, Complex.zero_im]
  split_ifs <;> simp

theorem shift_of_modeOf_ne {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) (d : L.Datum)
    (h : L.modeOf d ≠ 0) : L.pressureShift g x d = 0 := by
  rcases d with i | i | i | i | i | i | i | i <;>
    simp only [CellLayout.pressureShift, CellLayout.modeOf, Sum.elim_inl, Sum.elim_inr] at h ⊢
  rw [if_neg h]

theorem shift_of_plane {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) (d : L.Datum)
    (h : L.IsPlaneDeleted d) : L.pressureShift g x d = 0 := by
  rcases d with i | i | i | i | i | i | i | i <;>
    simp only [CellLayout.pressureShift, CellLayout.IsPlaneDeleted, Sum.elim_inl, Sum.elim_inr] at h ⊢

end ShiftedRealReduction.Internal

open ShiftedRealReduction.Internal in
theorem shiftedRealReduction_of (h1 : ConjugateDataStatement) (h2 : PlaneDeletedStatement) :
    ShiftedRealReductionStatement := by
  intro k N c K S B L g hL hg x hx hgd
  have hs := hL.modes_symm
  have hconj := h1 c K S B L hL x hx
  have hplane := h2 c K S B L hL x hx
  have hsh_plane : ∀ d, L.IsPlaneDeleted d → L.shiftedData g x d = 0 := fun d hd => by
    simp [CellLayout.shiftedData, hplane d hd, shift_of_plane L g x d hd]
  funext p
  obtain ⟨d, i⟩ := p
  unfold CellLayout.expandSystem
  split_ifs with hr hn
  · rfl
  · obtain ⟨hneg, -⟩ := hn
    have hm1 : L.modeOf d ≠ 0 := hneg.ne
    have hm2 : L.modeOf (L.conjDatum d) ≠ 0 := by rw [modeOf_conj L hs]; omega
    have e1 : L.shiftedData g x (L.conjDatum d) = (starRingEnd ℂ) (L.shiftedData g x d) := by
      simp only [CellLayout.shiftedData, shift_of_modeOf_ne L g x _ hm1, shift_of_modeOf_ne L g x _ hm2,
        hconj, add_zero]
    simp only [CellLayout.realPart, e1, CellLayout.partSign]
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
  · by_cases hp : L.IsPlaneDeleted d
    · simp [CellLayout.realPart, hsh_plane d hp]
    by_cases hG : L.IsGaugeDeleted d
    · simp [CellLayout.realPart, hgd d hG]
    have hr' : ¬ (0 < L.modeOf d ∨ (L.modeOf d = 0 ∧ i = 0)) := fun h => hr ⟨h, hp, hG⟩
    rcases lt_trichotomy (L.modeOf d) 0 with hlt | heq | hgt
    · exfalso
      apply hn
      refine ⟨hlt, ?_, ?_, ?_⟩
      · left
        show 0 < L.modeOf (L.conjDatum d)
        rw [modeOf_conj L hs]
        omega
      · rw [plane_conj]
        exact hp
      · intro hG'
        have h3 : L.modeOf (L.conjDatum d) = 0 := modeOf_of_gauge L _ hG'
        rw [modeOf_conj L hs] at h3
        exact hlt.ne (neg_eq_zero.mp h3)
    · have hi : i ≠ 0 := fun hi => hr' (Or.inr ⟨heq, hi⟩)
      have hc := hconj d
      rw [conj_of_modeOf_zero L d heq] at hc
      have him : (L.trueData x d).im = 0 := Complex.conj_eq_iff_im.mp hc.symm
      simp [CellLayout.realPart, hi, CellLayout.shiftedData, Complex.add_im, him, shift_im L g x d]
    · exact absurd (Or.inl hgt) hr'

end Breakdown.CellCert.CellFormula
