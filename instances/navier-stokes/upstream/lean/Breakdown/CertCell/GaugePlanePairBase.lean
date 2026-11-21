import Breakdown.CertCell.GaugePlaneFlipFacts
import Breakdown.CertCell.GaugePlanePairZero
import Breakdown.CertCell.ModeConjugate
import Breakdown.FracCell.ConjugateData

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown.CertCell.PlanePairInternal

open CellCert CellCert.CellCoordinates CellCert.CellFormula CellCert.CellAnalysis PlaneFlipFacts
open CellCert.CellFormula.ConjugateDataInternal

theorem ae_fst_ne_zero : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
  rw [ae_iff]
  have hs : {p : ℝ × ℝ | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp
  rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem heightStrip_congr {c o lo hi : ℝ} (wt t : ℝ → ℝ) {F F' dF dF' : ℝ × ℝ → ℂ} (hlo : 0 ≤ lo)
    (hF : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → F p = F' p)
    (hdF : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → dF p = dF' p) :
    heightStripMoment c o lo hi wt F dF t = heightStripMoment c o lo hi wt F' dF' t := by
  unfold heightStripMoment
  congr 1
  refine integral_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
  filter_upwards [hF, hdF, ae_fst_ne_zero] with p h1 h2 h3 hp
  have hpos : 0 < p.1 := lt_of_le_of_ne (le_trans hlo hp.1.1) (Ne.symm h3)
  rw [h1 hpos, h2 hpos]

theorem corner_congr {cr orr cz oz : ℝ} {F F' Fr Fr' Fz Fz' Frz Frz' : ℝ × ℝ → ℂ} (hmin : 0 ≤ min cr orr)
    (hF : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → F p = F' p)
    (hFr : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → Fr p = Fr' p)
    (hFz : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → Fz p = Fz' p)
    (hFrz : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → Frz p = Frz' p) :
    cornerMoment cr orr cz oz F Fr Fz Frz = cornerMoment cr orr cz oz F' Fr' Fz' Frz' := by
  unfold cornerMoment
  congr 1
  refine integral_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
  filter_upwards [hF, hFr, hFz, hFrz, ae_fst_ne_zero] with p h1 h2 h3 h4 h5 hp
  have hpos : 0 < p.1 := lt_of_le_of_ne (le_trans hmin hp.1.1) (Ne.symm h5)
  rw [h1 hpos, h2 hpos, h3 hpos, h4 hpos]

theorem heightStrip_of_le {c o lo hi : ℝ} (wt t : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (h : hi ≤ lo) :
    heightStripMoment c o lo hi wt F dF t = 0 := by
  have hz : (volume : Measure (ℝ × ℝ)) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ENNReal.ofReal_of_nonpos (by linarith),
      zero_mul]
  unfold heightStripMoment
  rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure, mul_zero]

theorem segTest_continuous (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

theorem flipLabel_of_fst {ξ : ℤ × ℤ} (h : ξ.1 = 0) : flipLabel ξ = -ξ := by
  ext <;> simp [flipLabel, h]

theorem planeLabel_fst (m : ℕ) (l : ℤ) : (labelHarmonic m (CellCalculus.harmonicMode 0 (2 * l))).1 = 0 := by
  have h : (2 * l + 0) / 2 = l := by omega
  simp only [labelHarmonic, labelTime, CellCalculus.harmonicMode, h]
  ring

section Conjugates

variable (ξ : ℤ × ℤ)

theorem planeVelocity_conj (v : ℝ → Space → Space) (a : Fin 3) :
    planeVelocity (-ξ) v a = fun p => conj (planeVelocity ξ v a p) := by
  funext p
  unfold planeVelocity
  rw [(Bridge.modeConjugate v (fun _ _ => 0) (fun _ _ => 0) ξ 0 (planePoint p)).1]
  rfl

theorem planeGrad_conj (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) :
    planeGrad (-ξ) G a b = fun p => conj (planeGrad ξ G a b p) := by
  funext p
  unfold planeGrad
  rw [(Bridge.modeConjugate (fun _ _ => 0) G (fun _ _ => 0) ξ 0 (planePoint p)).2.1]
  rfl

theorem planeSlope_conj (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) :
    planeSlope (-ξ) H a b c = fun p => conj (planeSlope ξ H a b c p) := by
  funext p
  unfold planeSlope
  rw [(Bridge.modeConjugate (fun _ _ => 0) (fun _ _ => 0) H ξ 0 (planePoint p)).2.2]
  rfl

end Conjugates

theorem modeVec_zero_field (m : ℕ) (n : ℤ) (r z : ℝ) (a : Fin 3) :
    modeVec m n (0 : Space → Space) r z a = 0 := by
  fin_cases a <;> simp [modeVec, frameVec]

theorem gradMode_zero_field (m : ℕ) (n : ℤ) (a b : Fin 3) (p : ℝ × ℝ) :
    gradMode m n (0 : Space → (Space →L[ℝ] Space)) a b p = 0 := by
  simp [gradMode, modeMat, frameMat]

theorem modeThird_zero_field (m : ℕ) (n : ℤ) (a b c : Fin 3) (p : ℝ × ℝ) :
    modeThird m n (0 : Space → (Space →L[ℝ] Space →L[ℝ] Space)) a b c p = 0 := by
  simp [modeThird, frameThird]

theorem lift_at_zero (hLift : CellCalculus.HarmonicLiftStatement) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : CellCalculus.IsPeriodicSecondOrder v G H) (Pg : ℝ → Space → Space) (L : CellLayout) (n : ℤ)
    (hn : Even n) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
      (∀ a, planeVelocity (labelHarmonic L.order (CellCalculus.harmonicMode 0 n)) v a p
          = L.velMode n (CellCalculus.cosTuple 0 v G H Pg) a p) ∧
      (∀ a b, planeGrad (labelHarmonic L.order (CellCalculus.harmonicMode 0 n)) G a b p
          = L.gradModeOf n (CellCalculus.cosTuple 0 v G H Pg) a b p) ∧
      (∀ a b c, planeSlope (labelHarmonic L.order (CellCalculus.harmonicMode 0 n)) H a b c p
          = L.secondModeOf n (CellCalculus.cosTuple 0 v G H Pg) a b c p) := by
  have h := (hLift L.order v G H hv 0).2.2 n (by simpa using hn)
  filter_upwards [h] with p hp hpos
  obtain ⟨h1, h2, h3⟩ := hp hpos
  refine ⟨fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · have e := h1 a
    rw [harmonicSin_at_zero, modeVec_zero_field, mul_zero, add_zero] at e
    exact e
  · have e := h2 a b
    rw [harmonicSin_at_zero, gradMode_zero_field, mul_zero, add_zero] at e
    exact e
  · have e := h3 a b c
    rw [harmonicSin_at_zero, modeThird_zero_field, mul_zero, add_zero] at e
    exact e

end Breakdown.CertCell.PlanePairInternal

