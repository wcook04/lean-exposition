import Breakdown.CertCell.GaugePlaneFlipFacts
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.CertCell.LocalResolvedEnergy

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace PlaneOdd.Internal

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellCoordinates CellCalculus LocalField PlaneFlipFacts

theorem box_null {lo hi : ℝ} (h : ¬ lo < hi) (s : Set ℝ) :
    (volume : Measure (ℝ × ℝ)) (Icc lo hi ×ˢ s) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  have h0 : (volume : Measure ℝ) (Icc lo hi) = 0 := by
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
    linarith [not_lt.mp h]
  rw [h0, zero_mul]

theorem strip_null (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) (h : ¬ lo < hi) :
    heightStripMoment c o lo hi wt F dF t = 0 := by
  unfold heightStripMoment
  rw [setIntegral_measure_zero _ (box_null h _), mul_zero]

theorem ae_fst_ne : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : (volume : Measure (ℝ × ℝ)) ({0} ×ˢ univ) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with p hp h0
  exact hp ⟨h0, trivial⟩

theorem ae_restrict_pos {P : ℝ × ℝ → Prop} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (h0 : ∀ p ∈ s, 0 ≤ p.1)
    (h : ∀ᵐ p ∂volume, 0 < p.1 → P p) : ∀ᵐ p ∂(volume.restrict s), P p := by
  rw [ae_restrict_iff' hs]
  filter_upwards [h, ae_fst_ne] with p hp hne hmem
  exact hp (lt_of_le_of_ne (h0 p hmem) (Ne.symm hne))

theorem setIntegral_combine {s : Set (ℝ × ℝ)} {f f₁ f₂ : ℝ × ℝ → ℂ} (h₁ : IntegrableOn f₁ s)
    (h₂ : IntegrableOn f₂ s) (he : ∀ᵐ p ∂(volume.restrict s), f p = f₁ p + Complex.I * f₂ p) :
    (∫ p in s, f₁ p) + Complex.I * ∫ p in s, f₂ p = ∫ p in s, f p := by
  rw [integral_congr_ae he, integral_add h₁ (h₂.const_mul Complex.I), integral_const_mul]

theorem strip_integrable {s : Set (ℝ × ℝ)} (hs : IsCompact s) {F dF : ℝ × ℝ → ℂ} (hF : IntegrableOn F s)
    (hdF : IntegrableOn dF s) (c o : ℝ) {wt t : ℝ → ℝ} (hwt : Continuous wt) (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((wt p.1 * t p.1 : ℝ) : ℂ)) s := by
  have h1 : ContinuousOn (fun _ : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ)) s := continuousOn_const
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (((p.2 - o) / (c - o) : ℝ) : ℂ)) s :=
    (Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)).continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ)) s :=
    (Complex.continuous_ofReal.comp ((hwt.comp continuous_fst).mul (ht.comp continuous_fst))).continuousOn
  exact ((hF.continuousOn_mul h1 hs).add (hdF.continuousOn_mul h2 hs)).mul_continuousOn h3 hs

theorem strip_weighted_integrable {s : Set (ℝ × ℝ)} (hs : IsCompact s) {F dF : ℝ × ℝ → ℂ}
    (hF : IntegrableOn F s) (hdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) s) (c o : ℝ) {t : ℝ → ℝ}
    (ht : Continuous t) (hm : MeasurableSet s) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((p.1 * t p.1 : ℝ) : ℂ)) s := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * ((p.1 * t p.1 : ℝ) : ℂ)) s :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_fst.mul (ht.comp continuous_fst)))).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((t p.1 : ℝ) : ℂ)) s :=
    ((Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)).mul
      (Complex.continuous_ofReal.comp (ht.comp continuous_fst))).continuousOn
  refine ((hF.continuousOn_mul h1 hs).add (hdF.continuousOn_mul h2 hs)).congr_fun (fun p _ => ?_) hm
  simp only [Pi.add_apply]
  push_cast
  ring

def cornerIntegrand (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun p => ((((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p
        + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p)

theorem cornerMoment_eq (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    cornerMoment cr orr cz oz F Fr Fz Frz = edgeSign cr orr * edgeSign cz oz *
      ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz),
        cornerIntegrand cr orr cz oz F Fr Fz Frz p := rfl

theorem corner_integrable {s : Set (ℝ × ℝ)} (hs : IsCompact s) {F Fr Fz Frz : ℝ × ℝ → ℂ}
    (hF : IntegrableOn F s) (hFr : IntegrableOn Fr s) (hFz : IntegrableOn Fz s) (hFrz : IntegrableOn Frz s)
    (cr orr cz oz : ℝ) : IntegrableOn (cornerIntegrand cr orr cz oz F Fr Fz Frz) s := by
  have cr1 : Continuous (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)
  have cz1 : Continuous (fun p : ℝ × ℝ => (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)
  exact (((hF.continuousOn_mul continuousOn_const hs).add
    (hFz.continuousOn_mul (continuous_const.mul cz1).continuousOn hs)).add
    (hFr.continuousOn_mul (cr1.mul continuous_const).continuousOn hs)).add
    (hFrz.continuousOn_mul (cr1.mul cz1).continuousOn hs)

theorem labelHarmonic_even (m : ℕ) {ν : ℤ} (hν : Even ν) : labelHarmonic m (harmonicMode ν 0) = (ν, 0) := by
  obtain ⟨r, rfl⟩ := hν
  unfold labelHarmonic labelTime labelAzimuth harmonicMode
  ext
  · show 2 * ((0 + (r + r)) / 2) - 0 = r + r
    omega
  · simp

theorem lift_even (hL : HarmonicLiftStatement) (m : ℕ) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsPeriodicSecondOrder v G H) {ν : ℤ} (hν : Even ν) :
    IsLocalSecondOrderField (harmonicCos ν v) (harmonicCos ν G) (harmonicCos ν H) ∧
    IsLocalSecondOrderField (harmonicSin ν v) (harmonicSin ν G) (harmonicSin ν H) ∧
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (∀ a, planeVelocity (ν, 0) v a p
          = modeVec m 0 (harmonicCos ν v) p.1 p.2 a + Complex.I * modeVec m 0 (harmonicSin ν v) p.1 p.2 a) ∧
      (∀ a b, planeGrad (ν, 0) G a b p
          = gradMode m 0 (harmonicCos ν G) a b p + Complex.I * gradMode m 0 (harmonicSin ν G) a b p) ∧
      (∀ a b c, planeSlope (ν, 0) H a b c p
          = modeThird m 0 (harmonicCos ν H) a b c p + Complex.I * modeThird m 0 (harmonicSin ν H) a b c p) := by
  obtain ⟨hc, hs, hae⟩ := hL m v G H hv ν
  have hl := labelHarmonic_even m hν
  refine ⟨hc, hs, ?_⟩
  filter_upwards [hae 0 (by rwa [zero_add])] with p hp hpos
  obtain ⟨e1, e2, e3⟩ := hp hpos
  refine ⟨fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · rw [← e1 a]
    simp only [planeVelocity, velAt, labelVel, hl]
  · rw [← e2 a b]
    simp only [planeGrad, gradAt, labelGrad, hl]
  · rw [← e3 a b c]
    simp only [planeSlope, slopeAt, labelHess, hl]

end PlaneOdd.Internal

end CertCell

end Breakdown
