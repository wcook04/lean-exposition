import Breakdown.CertCell.RowsMatchKeyFlipStatement
import Breakdown.CertCell.GaugePlanePair
import Breakdown.CertCell.GaugePlaneOddZero

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace KeyFlip.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellCoordinates CellCalculus LocalField PlaneFlipFacts PlaneOdd.Internal

variable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}

theorem even_neg {n ν : ℤ} (h : Even (n + ν)) : Even (-n + ν) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r - n, by omega⟩

theorem label_flip (m : ℕ) {ν n : ℤ} (h : Even (n + ν)) :
    labelHarmonic m (harmonicMode ν (-n)) = flipLabel (labelHarmonic m (harmonicMode ν n)) := by
  obtain ⟨r, hr⟩ := h
  simp only [labelHarmonic, labelTime, labelAzimuth, harmonicMode, flipLabel, Prod.mk.injEq]
  constructor
  · omega
  · ring

theorem frameSign_sq (a : Fin 3) : frameSign a * frameSign a = 1 := by
  unfold frameSign
  split_ifs <;> norm_num

theorem mode_int_n {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) (m : ℕ) (n : ℤ)
    {lo hi z₁ z₂ : ℝ} (hlo : 0 ≤ lo) :
    (∀ a, IntegrableOn (fun p : ℝ × ℝ => modeVec m n w p.1 p.2 a) (Icc lo hi ×ˢ Icc z₁ z₂)) ∧
      ∀ a b, IntegrableOn (gradMode m n Gw a b) (Icc lo hi ×ˢ Icc z₁ z₂) := by
  have hsub : Icc lo hi ×ˢ Icc z₁ z₂ ⊆ Icc 0 hi ×ˢ Icc z₁ z₂ := prod_mono (Icc_subset_Icc_left hlo) subset_rfl
  obtain ⟨h1, h2⟩ := localModeStripIntegrable m w Gw Hw hs n hi z₁ z₂
  exact ⟨fun a => (h1 a).mono_set hsub, fun a b => (h2 a b).mono_set hsub⟩

theorem third_sq_n {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) {K : CellBox}
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    AEStronglyMeasurable (modeThird m n Hw a b c) (volume.restrict K.rect) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeThird m n Hw a b c p‖ ^ 2) K.rect := by
  have e : comboThird (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) m n Hw c = modeThird m n Hw a b c := by
    funext p
    fin_cases a <;> fin_cases b <;> simp [comboThird, Fin.sum_univ_three]
  have h := (localModeSquareIntegrable K hK m w Gw Hw hs n (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0)).2.2 c
  rw [e] at h
  exact h

theorem third_weighted_n {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) {K : CellBox}
    (hK : IsCellBox K) (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n Hw a b c p) K.rect := by
  obtain ⟨hm, hi⟩ := third_sq_n hs hK m n a b c
  have hc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hr : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect := continuous_fst.continuousOn.integrableOn_compact hc
  refine Integrable.mono' ((hr.add hi).div_const 2)
    ((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hm) ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet K.rect)] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have hq : ‖modeThird m n Hw a b c p‖ ≤ (1 + ‖modeThird m n Hw a b c p‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖modeThird m n Hw a b c p‖ - 1)]
  calc p.1 * ‖modeThird m n Hw a b c p‖ ≤ p.1 * ((1 + ‖modeThird m n Hw a b c p‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hq h0
    _ = (p.1 + p.1 * ‖modeThird m n Hw a b c p‖ ^ 2) / 2 := by ring

theorem third_plain_n {w : Space → Space} {Gw : Space → (Space →L[ℝ] Space)}
    {Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField w Gw Hw) {K : CellBox}
    (hK : IsCellBox K) (hpos : 0 < K.r₁) (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    IntegrableOn (modeThird m n Hw a b c) K.rect := by
  obtain ⟨hm, hi⟩ := third_sq_n hs hK m n a b c
  have hc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ)) K.rect := continuousOn_const.integrableOn_compact hc
  refine Integrable.mono' ((h1.add (hi.div_const K.r₁)).div_const 2) hm ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet K.rect)] with p hp
  have hp1 : K.r₁ ≤ p.1 := hp.1.1
  have hq : ‖modeThird m n Hw a b c p‖ ≤ (1 + ‖modeThird m n Hw a b c p‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖modeThird m n Hw a b c p‖ - 1)]
  have hs2 : ‖modeThird m n Hw a b c p‖ ^ 2 ≤ p.1 * ‖modeThird m n Hw a b c p‖ ^ 2 / K.r₁ := by
    rw [le_div_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left hp1 (sq_nonneg _) |>.trans_eq (mul_comm _ _)
  calc ‖modeThird m n Hw a b c p‖ ≤ (1 + ‖modeThird m n Hw a b c p‖ ^ 2) / 2 := hq
    _ ≤ (1 + p.1 * ‖modeThird m n Hw a b c p‖ ^ 2 / K.r₁) / 2 := by linarith

theorem lift_gen (hL : HarmonicLiftStatement) (m : ℕ) (hv : IsPeriodicSecondOrder v G H) {ν n : ℤ}
    (hn : Even (n + ν)) :
    IsLocalSecondOrderField (harmonicCos ν v) (harmonicCos ν G) (harmonicCos ν H) ∧
    IsLocalSecondOrderField (harmonicSin ν v) (harmonicSin ν G) (harmonicSin ν H) ∧
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (∀ a, planeVelocity (labelHarmonic m (harmonicMode ν n)) v a p
          = modeVec m n (harmonicCos ν v) p.1 p.2 a + Complex.I * modeVec m n (harmonicSin ν v) p.1 p.2 a) ∧
      (∀ a b, planeGrad (labelHarmonic m (harmonicMode ν n)) G a b p
          = gradMode m n (harmonicCos ν G) a b p + Complex.I * gradMode m n (harmonicSin ν G) a b p) ∧
      (∀ a b c, planeSlope (labelHarmonic m (harmonicMode ν n)) H a b c p
          = modeThird m n (harmonicCos ν H) a b c p + Complex.I * modeThird m n (harmonicSin ν H) a b c p) := by
  obtain ⟨hc, hs, hae⟩ := hL m v G H hv ν
  refine ⟨hc, hs, ?_⟩
  filter_upwards [hae n hn] with p hp hpos
  obtain ⟨e1, e2, e3⟩ := hp hpos
  refine ⟨fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · rw [← e1 a]
    simp only [planeVelocity, velAt, labelVel]
  · rw [← e2 a b]
    simp only [planeGrad, gradAt, labelGrad]
  · rw [← e3 a b c]
    simp only [planeSlope, slopeAt, labelHess]

def stripVel (m : ℕ) (ν n : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (a : Fin 3)
    (lo hi h : ℝ) (wt t : ℝ → ℝ) : ℂ :=
  heightStripMoment 0 h lo hi wt (fun p => modeVec m n (harmonicCos ν v) p.1 p.2 a)
      (gradMode m n (harmonicCos ν G) a 2) t
    + Complex.I * heightStripMoment 0 h lo hi wt (fun p => modeVec m n (harmonicSin ν v) p.1 p.2 a)
      (gradMode m n (harmonicSin ν G) a 2) t

def stripGrad (m : ℕ) (ν n : ℤ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (lo hi h : ℝ) (t : ℝ → ℝ) : ℂ :=
  heightStripMoment 0 h lo hi (fun r => r) (gradMode m n (harmonicCos ν G) a 2)
      (modeThird m n (harmonicCos ν H) a 2 2) t
    + Complex.I * heightStripMoment 0 h lo hi (fun r => r) (gradMode m n (harmonicSin ν G) a 2)
      (modeThird m n (harmonicSin ν H) a 2 2) t

def cornerVal (m : ℕ) (ν n : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (cr h : ℝ) : ℂ :=
  cornerMoment cr (cr + 1) 0 h (fun p => modeVec m n (harmonicCos ν v) p.1 p.2 a)
      (gradMode m n (harmonicCos ν G) a 0) (gradMode m n (harmonicCos ν G) a 2)
      (modeThird m n (harmonicCos ν H) a 0 2)
    + Complex.I * cornerMoment cr (cr + 1) 0 h (fun p => modeVec m n (harmonicSin ν v) p.1 p.2 a)
      (gradMode m n (harmonicSin ν G) a 0) (gradMode m n (harmonicSin ν G) a 2)
      (modeThird m n (harmonicSin ν H) a 0 2)

theorem stripVel_as_plane (hL : HarmonicLiftStatement) (hv : IsPeriodicSecondOrder v G H) (m : ℕ) {ν n : ℤ}
    (hn : Even (n + ν)) (a : Fin 3) {lo hi h : ℝ} (hlo : 0 ≤ lo) {wt t : ℝ → ℝ} (hwt : Continuous wt)
    (ht : Continuous t) :
    stripVel m ν n v G a lo hi h wt t
      = heightStripMoment 0 h lo hi wt (planeVelocity (labelHarmonic m (harmonicMode ν n)) v a)
          (planeGrad (labelHarmonic m (harmonicMode ν n)) G a 2) t := by
  obtain ⟨hc, hs, hae⟩ := lift_gen hL m hv hn
  have hK : IsCompact (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := isCompact_Icc.prod isCompact_Icc
  have hM : MeasurableSet (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨cV, cG⟩ := mode_int_n hc m n (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  obtain ⟨sV, sG⟩ := mode_int_n hs m n (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  exact strip_combine (strip_integrable hK (cV a) (cG a 2) 0 h hwt ht) (strip_integrable hK (sV a) (sG a 2) 0 h hwt ht)
    (by
      filter_upwards [ae_restrict_pos hM (fun p hp => hlo.trans hp.1.1) hae] with p hp
      exact ⟨hp.1 a, hp.2.1 a 2⟩)

theorem stripGrad_as_plane (hL : HarmonicLiftStatement) (hv : IsPeriodicSecondOrder v G H) (m : ℕ) {ν n : ℤ}
    (hn : Even (n + ν)) (a : Fin 3) {lo hi h : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi) (hh : 0 < h) {t : ℝ → ℝ}
    (ht : Continuous t) :
    stripGrad m ν n G H a lo hi h t
      = heightStripMoment 0 h lo hi (fun r => r) (planeGrad (labelHarmonic m (harmonicMode ν n)) G a 2)
          (planeSlope (labelHarmonic m (harmonicMode ν n)) H a 2 2) t := by
  obtain ⟨hc, hs, hae⟩ := lift_gen hL m hv hn
  have hK : IsCompact (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := isCompact_Icc.prod isCompact_Icc
  have hM : MeasurableSet (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := measurableSet_Icc.prod measurableSet_Icc
  have hbox : IsCellBox ⟨lo, hi, min 0 h, max 0 h⟩ :=
    ⟨⟨hlo, hlh⟩, ⟨le_min le_rfl hh.le, min_lt_max.2 hh.ne⟩⟩
  obtain ⟨-, cG⟩ := mode_int_n hc m n (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  obtain ⟨-, sG⟩ := mode_int_n hs m n (hi := hi) (z₁ := min 0 h) (z₂ := max 0 h) hlo
  exact strip_combine (wt := fun r => r)
    (strip_weighted_integrable hK (cG a 2) (third_weighted_n hc hbox m n a 2 2) 0 h ht hM)
    (strip_weighted_integrable hK (sG a 2) (third_weighted_n hs hbox m n a 2 2) 0 h ht hM)
    (by
      filter_upwards [ae_restrict_pos hM (fun p hp => hlo.trans hp.1.1) hae] with p hp
      exact ⟨hp.2.1 a 2, hp.2.2 a 2 2⟩)

theorem cornerVal_as_plane (hL : HarmonicLiftStatement) (hv : IsPeriodicSecondOrder v G H) (m : ℕ) {ν n : ℤ}
    (hn : Even (n + ν)) (a : Fin 3) {cr h : ℝ} (hcr : 0 < cr) (hh : 0 < h) :
    cornerVal m ν n v G H a cr h
      = cornerMoment cr (cr + 1) 0 h (planeVelocity (labelHarmonic m (harmonicMode ν n)) v a)
          (planeGrad (labelHarmonic m (harmonicMode ν n)) G a 0) (planeGrad (labelHarmonic m (harmonicMode ν n)) G a 2)
          (planeSlope (labelHarmonic m (harmonicMode ν n)) H a 0 2) := by
  obtain ⟨hc, hs, hae⟩ := lift_gen hL m hv hn
  have hne : cr ≠ cr + 1 := ne_of_lt (lt_add_one cr)
  have hK : IsCompact (Icc (min cr (cr + 1)) (max cr (cr + 1)) ×ˢ Icc (min 0 h) (max 0 h)) :=
    isCompact_Icc.prod isCompact_Icc
  have hM : MeasurableSet (Icc (min cr (cr + 1)) (max cr (cr + 1)) ×ˢ Icc (min 0 h) (max 0 h)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hlo : 0 < min cr (cr + 1) := lt_min hcr (by linarith)
  have hbox : IsCellBox ⟨min cr (cr + 1), max cr (cr + 1), min 0 h, max 0 h⟩ :=
    ⟨⟨hlo.le, min_lt_max.2 hne⟩, ⟨le_min le_rfl hh.le, min_lt_max.2 hh.ne⟩⟩
  obtain ⟨cV, cG⟩ := mode_int_n hc m n (hi := max cr (cr + 1)) (z₁ := min 0 h) (z₂ := max 0 h) hlo.le
  obtain ⟨sV, sG⟩ := mode_int_n hs m n (hi := max cr (cr + 1)) (z₁ := min 0 h) (z₂ := max 0 h) hlo.le
  exact corner_combine
    (corner_integrable hK (cV a) (cG a 0) (cG a 2) (third_plain_n hc hbox hlo m n a 0 2) _ _ _ _)
    (corner_integrable hK (sV a) (sG a 0) (sG a 2) (third_plain_n hs hbox hlo m n a 0 2) _ _ _ _)
    (by
      filter_upwards [ae_restrict_pos hM (fun p hp => hlo.le.trans hp.1.1) hae] with p hp
      exact ⟨hp.1 a, hp.2.1 a 0, hp.2.1 a 2, hp.2.2 a 0 2⟩)

end KeyFlip.Internal

end CertCell

end Breakdown
