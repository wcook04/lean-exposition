import Breakdown.CertCell.GaugePlaneOddMain

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace PlaneOdd.Internal

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellCoordinates CellCalculus LocalField PlaneFlipFacts

variable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}

theorem strip_velocity_zero (hS : StripDataFlipAxisHolds) (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds)
    (hp : IsPerturbation Γ P v G H g) (hf : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (m : ℕ) {ν : ℤ}
    (hν : Even ν) (a : Fin 3) (ha : frameSign a = -1) {lo hi h : ℝ} (hlo : 0 ≤ lo) (hh : 0 < h)
    {wt t : ℝ → ℝ} (hwt : Continuous wt) (ht : Continuous t) :
    heightStripMoment 0 h lo hi wt (fun p => modeVec m 0 (harmonicCos ν v) p.1 p.2 a)
        (gradMode m 0 (harmonicCos ν G) a 2) t
      + Complex.I * heightStripMoment 0 h lo hi wt (fun p => modeVec m 0 (harmonicSin ν v) p.1 p.2 a)
        (gradMode m 0 (harmonicSin ν G) a 2) t = 0 := by
  by_cases hlh : lo < hi
  swap
  · rw [strip_null _ _ _ _ _ _ _ _ hlh, strip_null _ _ _ _ _ _ _ _ hlh, mul_zero, add_zero]
  obtain ⟨hc, hs, hae⟩ := lift_even hL m (hP Γ P v G H g hp) hν
  have hK : IsCompact (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := isCompact_Icc.prod isCompact_Icc
  have hM : MeasurableSet (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨cV, cG⟩ := mode_int hc m (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  obtain ⟨sV, sG⟩ := mode_int hs m (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  rw [strip_combine (F := planeVelocity (ν, 0) v a) (dF := planeGrad (ν, 0) G a 2)
    (strip_integrable hK (cV a) (cG a 2) 0 h hwt ht) (strip_integrable hK (sV a) (sG a 2) 0 h hwt ht)
    (by
      filter_upwards [ae_restrict_pos hM (fun p hp => hlo.trans hp.1.1) hae] with p hp
      exact ⟨hp.1 a, hp.2.1 a 2⟩)]
  have e := (hS Γ P v G H g hp hf (ν, 0) a lo hi h h wt t hlo hlh hh hh hwt ht).1
  rw [flipLabel_axis, ha] at e
  push_cast at e
  linear_combination e / 2

theorem strip_gradient_zero (hS : StripDataFlipAxisHolds) (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds)
    (hp : IsPerturbation Γ P v G H g) (hf : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (m : ℕ) {ν : ℤ}
    (hν : Even ν) (a : Fin 3) (ha : frameSign a = 1) {lo hi h : ℝ} (hlo : 0 ≤ lo) (hh : 0 < h)
    {t : ℝ → ℝ} (ht : Continuous t) :
    heightStripMoment 0 h lo hi (fun r => r) (gradMode m 0 (harmonicCos ν G) a 2)
        (modeThird m 0 (harmonicCos ν H) a 2 2) t
      + Complex.I * heightStripMoment 0 h lo hi (fun r => r) (gradMode m 0 (harmonicSin ν G) a 2)
        (modeThird m 0 (harmonicSin ν H) a 2 2) t = 0 := by
  by_cases hlh : lo < hi
  swap
  · rw [strip_null _ _ _ _ _ _ _ _ hlh, strip_null _ _ _ _ _ _ _ _ hlh, mul_zero, add_zero]
  obtain ⟨hc, hs, hae⟩ := lift_even hL m (hP Γ P v G H g hp) hν
  have hK : IsCompact (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := isCompact_Icc.prod isCompact_Icc
  have hM : MeasurableSet (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := measurableSet_Icc.prod measurableSet_Icc
  have hbox : IsCellBox ⟨lo, hi, min 0 h, max 0 h⟩ :=
    ⟨⟨hlo, hlh⟩, ⟨le_min le_rfl hh.le, min_lt_max.2 hh.ne⟩⟩
  obtain ⟨-, cG⟩ := mode_int hc m (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  obtain ⟨-, sG⟩ := mode_int hs m (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  rw [strip_combine (wt := fun r => r) (F := planeGrad (ν, 0) G a 2) (dF := planeSlope (ν, 0) H a 2 2)
    (strip_weighted_integrable hK (cG a 2) (third_weighted hc hbox m a 2 2) 0 h ht hM)
    (strip_weighted_integrable hK (sG a 2) (third_weighted hs hbox m a 2 2) 0 h ht hM)
    (by
      filter_upwards [ae_restrict_pos hM (fun p hp => hlo.trans hp.1.1) hae] with p hp
      exact ⟨hp.2.1 a 2, hp.2.2 a 2 2⟩)]
  have e := (hS Γ P v G H g hp hf (ν, 0) a lo hi h h (fun r => r) t hlo hlh hh hh continuous_id ht).2
    (axis_admissible hlo ht)
  rw [flipLabel_axis, ha] at e
  push_cast at e
  linear_combination e / 2

theorem corner_zero (hC : CornerDataFlipAxisHolds) (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds)
    (hp : IsPerturbation Γ P v G H g) (hf : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (m : ℕ) {ν : ℤ}
    (hν : Even ν) (a : Fin 3) (ha : frameSign a = -1) {cr h : ℝ} (hcr : 0 < cr) (hh : 0 < h) :
    cornerMoment cr (cr + 1) 0 h (fun p => modeVec m 0 (harmonicCos ν v) p.1 p.2 a)
        (gradMode m 0 (harmonicCos ν G) a 0) (gradMode m 0 (harmonicCos ν G) a 2)
        (modeThird m 0 (harmonicCos ν H) a 0 2)
      + Complex.I * cornerMoment cr (cr + 1) 0 h (fun p => modeVec m 0 (harmonicSin ν v) p.1 p.2 a)
        (gradMode m 0 (harmonicSin ν G) a 0) (gradMode m 0 (harmonicSin ν G) a 2)
        (modeThird m 0 (harmonicSin ν H) a 0 2) = 0 := by
  obtain ⟨hc, hs, hae⟩ := lift_even hL m (hP Γ P v G H g hp) hν
  have hne : cr ≠ cr + 1 := ne_of_lt (lt_add_one cr)
  have hK : IsCompact (Icc (min cr (cr + 1)) (max cr (cr + 1)) ×ˢ Icc (min 0 h) (max 0 h)) :=
    isCompact_Icc.prod isCompact_Icc
  have hM : MeasurableSet (Icc (min cr (cr + 1)) (max cr (cr + 1)) ×ˢ Icc (min 0 h) (max 0 h)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hlo : 0 < min cr (cr + 1) := lt_min hcr (by linarith)
  have hbox : IsCellBox ⟨min cr (cr + 1), max cr (cr + 1), min 0 h, max 0 h⟩ :=
    ⟨⟨hlo.le, min_lt_max.2 hne⟩, ⟨le_min le_rfl hh.le, min_lt_max.2 hh.ne⟩⟩
  obtain ⟨cV, cG⟩ := mode_int hc m (hi := max cr (cr + 1)) (z₁ := min 0 h) (z₂ := max 0 h) hlo.le
  obtain ⟨sV, sG⟩ := mode_int hs m (hi := max cr (cr + 1)) (z₁ := min 0 h) (z₂ := max 0 h) hlo.le
  rw [corner_combine (F := planeVelocity (ν, 0) v a) (Fr := planeGrad (ν, 0) G a 0) (Fz := planeGrad (ν, 0) G a 2)
    (Frz := planeSlope (ν, 0) H a 0 2)
    (corner_integrable hK (cV a) (cG a 0) (cG a 2) (third_plain hc hbox hlo m a 0 2) _ _ _ _)
    (corner_integrable hK (sV a) (sG a 0) (sG a 2) (third_plain hs hbox hlo m a 0 2) _ _ _ _)
    (by
      filter_upwards [ae_restrict_pos hM (fun p hp => hlo.le.trans hp.1.1) hae] with p hp
      exact ⟨hp.1 a, hp.2.1 a 0, hp.2.1 a 2, hp.2.2 a 0 2⟩)]
  have e := hC Γ P v G H g hp hf (ν, 0) a cr (cr + 1) h h hcr (by linarith) hne hh hh
  rw [flipLabel_axis, ha] at e
  push_cast at e
  linear_combination e / 2

end PlaneOdd.Internal

end CertCell

end Breakdown
