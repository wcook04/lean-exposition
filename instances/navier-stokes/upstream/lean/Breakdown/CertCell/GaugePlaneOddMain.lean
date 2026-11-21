import Breakdown.CertCell.GaugePlaneOddCore

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace PlaneOdd.Internal

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellCoordinates CellCalculus LocalField PlaneFlipFacts

theorem flipLabel_axis (ν : ℤ) : flipLabel ((ν, 0) : ℤ × ℤ) = (ν, 0) := by
  unfold flipLabel
  ext <;> simp

theorem axis_admissible {lo : ℝ} (hlo : 0 ≤ lo) {t : ℝ → ℝ} (ht : Continuous t) :
    IsAxisAdmissibleTest lo (fun r => r * t r) := by
  rcases hlo.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.symm, t, ht, fun _ => rfl⟩

theorem test_cont (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  fun_prop

theorem strip_combine {c o lo hi : ℝ} {wt t : ℝ → ℝ} {F dF F₁ dF₁ F₂ dF₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F₁ p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF₁ p)
      * ((wt p.1 * t p.1 : ℝ) : ℂ)) (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (h₂ : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F₂ p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF₂ p)
      * ((wt p.1 * t p.1 : ℝ) : ℂ)) (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (he : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc (min c o) (max c o))),
      F p = F₁ p + Complex.I * F₂ p ∧ dF p = dF₁ p + Complex.I * dF₂ p) :
    heightStripMoment c o lo hi wt F₁ dF₁ t + Complex.I * heightStripMoment c o lo hi wt F₂ dF₂ t
      = heightStripMoment c o lo hi wt F dF t := by
  have e := setIntegral_combine h₁ h₂ (f := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * t p.1 : ℝ) : ℂ)) (by
    filter_upwards [he] with p hp
    rw [hp.1, hp.2]
    ring)
  unfold heightStripMoment
  rw [← e]
  ring

theorem corner_combine {cr orr cz oz : ℝ} {F Fr Fz Frz F₁ Fr₁ Fz₁ Frz₁ F₂ Fr₂ Fz₂ Frz₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn (cornerIntegrand cr orr cz oz F₁ Fr₁ Fz₁ Frz₁)
      (Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz)))
    (h₂ : IntegrableOn (cornerIntegrand cr orr cz oz F₂ Fr₂ Fz₂ Frz₂)
      (Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz)))
    (he : ∀ᵐ p ∂(volume.restrict (Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz))),
      F p = F₁ p + Complex.I * F₂ p ∧ Fr p = Fr₁ p + Complex.I * Fr₂ p ∧ Fz p = Fz₁ p + Complex.I * Fz₂ p ∧
        Frz p = Frz₁ p + Complex.I * Frz₂ p) :
    cornerMoment cr orr cz oz F₁ Fr₁ Fz₁ Frz₁ + Complex.I * cornerMoment cr orr cz oz F₂ Fr₂ Fz₂ Frz₂
      = cornerMoment cr orr cz oz F Fr Fz Frz := by
  have e := setIntegral_combine h₁ h₂ (f := cornerIntegrand cr orr cz oz F Fr Fz Frz) (by
    filter_upwards [he] with p hp
    simp only [cornerIntegrand]
    rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
    ring)
  rw [cornerMoment_eq, cornerMoment_eq, cornerMoment_eq, ← e]
  ring

theorem mode_int {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) (m : ℕ)
    {lo hi z₁ z₂ : ℝ} (hlo : 0 ≤ lo) :
    (∀ a, IntegrableOn (fun p : ℝ × ℝ => modeVec m 0 w p.1 p.2 a) (Icc lo hi ×ˢ Icc z₁ z₂)) ∧
      ∀ a b, IntegrableOn (gradMode m 0 Gw a b) (Icc lo hi ×ˢ Icc z₁ z₂) := by
  have hsub : Icc lo hi ×ˢ Icc z₁ z₂ ⊆ Icc 0 hi ×ˢ Icc z₁ z₂ := prod_mono (Icc_subset_Icc_left hlo) subset_rfl
  obtain ⟨h1, h2⟩ := localModeStripIntegrable m w Gw Hw hs 0 hi z₁ z₂
  exact ⟨fun a => (h1 a).mono_set hsub, fun a b => (h2 a b).mono_set hsub⟩

theorem third_sq {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) {K : CellBox}
    (hK : IsCellBox K) (m : ℕ) (a b c : Fin 3) :
    AEStronglyMeasurable (modeThird m 0 Hw a b c) (volume.restrict K.rect) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeThird m 0 Hw a b c p‖ ^ 2) K.rect := by
  have e : comboThird (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) m 0 Hw c = modeThird m 0 Hw a b c := by
    funext p
    fin_cases a <;> fin_cases b <;> simp [comboThird, Fin.sum_univ_three]
  have h := (localModeSquareIntegrable K hK m w Gw Hw hs 0 (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0)).2.2 c
  rw [e] at h
  exact h

theorem third_weighted {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) {K : CellBox}
    (hK : IsCellBox K) (m : ℕ) (a b c : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m 0 Hw a b c p) K.rect := by
  obtain ⟨hm, hi⟩ := third_sq hs hK m a b c
  have hc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hr : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect := continuous_fst.continuousOn.integrableOn_compact hc
  refine Integrable.mono' ((hr.add hi).div_const 2)
    ((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hm) ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet K.rect)] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have hq : ‖modeThird m 0 Hw a b c p‖ ≤ (1 + ‖modeThird m 0 Hw a b c p‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖modeThird m 0 Hw a b c p‖ - 1)]
  calc p.1 * ‖modeThird m 0 Hw a b c p‖ ≤ p.1 * ((1 + ‖modeThird m 0 Hw a b c p‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hq h0
    _ = (p.1 + p.1 * ‖modeThird m 0 Hw a b c p‖ ^ 2) / 2 := by ring

theorem third_plain {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) {K : CellBox}
    (hK : IsCellBox K) (hpos : 0 < K.r₁) (m : ℕ) (a b c : Fin 3) :
    IntegrableOn (modeThird m 0 Hw a b c) K.rect := by
  obtain ⟨hm, hi⟩ := third_sq hs hK m a b c
  have hc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ)) K.rect := continuousOn_const.integrableOn_compact hc
  refine Integrable.mono' ((h1.add (hi.div_const K.r₁)).div_const 2) hm ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet K.rect)] with p hp
  have hp1 : K.r₁ ≤ p.1 := hp.1.1
  have hq : ‖modeThird m 0 Hw a b c p‖ ≤ (1 + ‖modeThird m 0 Hw a b c p‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖modeThird m 0 Hw a b c p‖ - 1)]
  have hs2 : ‖modeThird m 0 Hw a b c p‖ ^ 2 ≤ p.1 * ‖modeThird m 0 Hw a b c p‖ ^ 2 / K.r₁ := by
    rw [le_div_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left hp1 (sq_nonneg _) |>.trans_eq (mul_comm _ _)
  calc ‖modeThird m 0 Hw a b c p‖ ≤ (1 + ‖modeThird m 0 Hw a b c p‖ ^ 2) / 2 := hq
    _ ≤ (1 + p.1 * ‖modeThird m 0 Hw a b c p‖ ^ 2 / K.r₁) / 2 := by linarith
end PlaneOdd.Internal

end CertCell

end Breakdown
