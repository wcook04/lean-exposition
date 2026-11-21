import Breakdown.CertCell.GaugePlanePairBase

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown.CertCell

namespace PlanePairInternal

open CellCert CellCert.CellCoordinates CellCert.CellFormula CellCert.CellAnalysis PlaneFlipFacts
open CellCert.CellFormula.ConjugateDataInternal

section Unfold

variable (L : CellLayout) {j : ℕ} (x : Assembly.FieldTuple j) (n : ℤ) (lo hi : ℝ) (t : ℕ → ℕ → ℝ)

theorem keyValue_velocity_plane (a : Fin 3) (d : ℕ) :
    keyValue L x (SkeletonKey.velocity n false 0 lo hi t a d)
      = heightStripMoment 0 1 lo hi (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2)
          ((keySeg false 0 lo hi t).test d) := by
  simp only [keyValue, FaceSegment.moment, keySeg, Bool.false_eq_true, if_false, zero_add]

theorem keyValue_gradient_plane (a : Fin 3) (d : ℕ) :
    keyValue L x (SkeletonKey.gradient n false 0 lo hi t a d)
      = heightStripMoment 0 1 lo hi (fun r => r) (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 2)
          ((keySeg false 0 lo hi t).test d) := by
  simp only [keyValue, FaceSegment.moment, keySeg, Bool.false_eq_true, if_false, if_true, zero_add]

theorem keyValue_pressure_plane (d : ℕ) :
    keyValue L x (SkeletonKey.pressure n false 0 lo hi t d)
      = heightStripMoment 0 1 lo hi (fun r => r) (headPressure L n x) (L.pressureGradMode n x 2)
          ((keySeg false 0 lo hi t).test d) := by
  simp only [keyValue, FaceSegment.moment, keySeg, Bool.false_eq_true, if_false, if_true, zero_add]

theorem keyValue_corner_plane (pr : ℝ) (a : Fin 3) :
    keyValue L x (SkeletonKey.corner n (pr, 0) a)
      = cornerMoment pr (pr + 1) 0 1 (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
          (L.secondModeOf n x a 0 2) := by
  simp only [keyValue, zero_add]

end Unfold

theorem axisAdmissible_of_nonneg {lo : ℝ} (hlo : 0 ≤ lo) {t : ℝ → ℝ} (ht : Continuous t) :
    IsAxisAdmissibleTest lo (fun r => r * t r) := by
  rcases hlo.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.symm, t, ht, fun _ => rfl⟩

theorem keyPart_zero_of_conj {z : ℂ} {s : ℝ} (h : conj z = (s : ℂ) * z) {imag : Bool}
    (hs : (s = 1 ∧ imag = true) ∨ (s = -1 ∧ imag = false)) : GaugeKey.keyPart imag z = 0 := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e := congrArg Complex.im h
    simp only [Complex.conj_im, Complex.ofReal_one, one_mul] at e
    show z.im = 0
    linarith
  · have e := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, Complex.neg_re] at e
    show z.re = 0
    linarith

section Keys

variable (hLift : CellCalculus.HarmonicLiftStatement) (hSec : PeriodicSecondOrderHolds)
  {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} (Pg : ℝ → Space → Space)
  (hp : IsPerturbation Γ P v G H g) (hfl : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (L : CellLayout)
  (l : ℤ)

include hLift hSec hp hfl

theorem velocity_key_conj (hStrip : StripDataFlipAxisHolds) {lo : ℝ} (hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3)
    (d : ℕ) (hlo : 0 ≤ lo) :
    conj (keyValue L (CellCalculus.cosTuple 0 v G H Pg) (SkeletonKey.velocity (2 * l) false 0 lo hi t a d))
      = (frameSign a : ℂ) * keyValue L (CellCalculus.cosTuple 0 v G H Pg)
          (SkeletonKey.velocity (2 * l) false 0 lo hi t a d) := by
  have hξ := flipLabel_of_fst (planeLabel_fst L.order l)
  have hL := lift_at_zero hLift (hSec Γ P v G H g hp) Pg L (2 * l) (even_two_mul l)
  have hS := segTest_continuous (keySeg false 0 lo hi t) d
  rw [keyValue_velocity_plane]
  rcases lt_or_ge lo hi with hlh | hlh
  · have e := (hStrip Γ P v G H g hp hfl (labelHarmonic L.order (CellCalculus.harmonicMode 0 (2 * l))) a lo hi
      1 1 (fun _ => 1) _ hlo hlh one_pos one_pos continuous_const hS).1
    rw [hξ, planeVelocity_conj, planeGrad_conj, ← conj_heightStrip] at e
    rw [heightStrip_congr _ _ hlo (hL.mono fun p hq hpos => ((hq hpos).1 a).symm)
      (hL.mono fun p hq hpos => ((hq hpos).2.1 a 2).symm)]
    exact e
  · rw [heightStrip_of_le _ _ _ _ hlh, map_zero, mul_zero]

theorem gradient_key_conj (hStrip : StripDataFlipAxisHolds) {lo : ℝ} (hi : ℝ) (t : ℕ → ℕ → ℝ) (a : Fin 3)
    (d : ℕ) (hlo : 0 ≤ lo) :
    conj (keyValue L (CellCalculus.cosTuple 0 v G H Pg) (SkeletonKey.gradient (2 * l) false 0 lo hi t a d))
      = ((-frameSign a : ℝ) : ℂ) * keyValue L (CellCalculus.cosTuple 0 v G H Pg)
          (SkeletonKey.gradient (2 * l) false 0 lo hi t a d) := by
  have hξ := flipLabel_of_fst (planeLabel_fst L.order l)
  have hL := lift_at_zero hLift (hSec Γ P v G H g hp) Pg L (2 * l) (even_two_mul l)
  have hS := segTest_continuous (keySeg false 0 lo hi t) d
  rw [keyValue_gradient_plane]
  rcases lt_or_ge lo hi with hlh | hlh
  · have e := (hStrip Γ P v G H g hp hfl (labelHarmonic L.order (CellCalculus.harmonicMode 0 (2 * l))) a lo hi
      1 1 (fun r => r) _ hlo hlh one_pos one_pos continuous_id hS).2 (axisAdmissible_of_nonneg hlo hS)
    rw [hξ, planeGrad_conj, planeSlope_conj, ← conj_heightStrip] at e
    rw [heightStrip_congr _ _ hlo (hL.mono fun p hq hpos => ((hq hpos).2.1 a 2).symm)
      (hL.mono fun p hq hpos => ((hq hpos).2.2 a 2 2).symm), e]
    push_cast
    ring
  · rw [heightStrip_of_le _ _ _ _ hlh, map_zero, mul_zero]

theorem corner_key_conj (hCorner : CornerDataFlipAxisHolds) {pr : ℝ} (a : Fin 3) (hpr : 0 < pr) :
    conj (keyValue L (CellCalculus.cosTuple 0 v G H Pg) (SkeletonKey.corner (2 * l) (pr, 0) a))
      = (frameSign a : ℂ) * keyValue L (CellCalculus.cosTuple 0 v G H Pg) (SkeletonKey.corner (2 * l) (pr, 0) a) := by
  have hξ := flipLabel_of_fst (planeLabel_fst L.order l)
  have hL := lift_at_zero hLift (hSec Γ P v G H g hp) Pg L (2 * l) (even_two_mul l)
  rw [keyValue_corner_plane]
  have e := hCorner Γ P v G H g hp hfl (labelHarmonic L.order (CellCalculus.harmonicMode 0 (2 * l))) a pr (pr + 1)
    1 1 hpr (by linarith) (ne_of_lt (by linarith)) one_pos one_pos
  rw [hξ, planeVelocity_conj, planeGrad_conj, planeGrad_conj, planeSlope_conj, ← conj_corner] at e
  rw [corner_congr (le_min hpr.le (by linarith)) (hL.mono fun p hq hpos => ((hq hpos).1 a).symm)
    (hL.mono fun p hq hpos => ((hq hpos).2.1 a 0).symm) (hL.mono fun p hq hpos => ((hq hpos).2.1 a 2).symm)
    (hL.mono fun p hq hpos => ((hq hpos).2.2 a 0 2).symm)]
  exact e

end Keys

theorem pressure_key_conj (hPS : PressureStripFlipHolds) (hShift : PotentialShiftHolds)
    (hSq : HarmonicPressureSquareHolds) (hHF : HarmonicPressureFlipHolds) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {Pg : ℝ → Space → Space} (hPP : CellCalculus.IsPeriodicPressure Pg)
    (hPf : ∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)) (L : CellLayout) (n : ℤ)
    {lo : ℝ} (hi : ℝ) (t : ℕ → ℕ → ℝ) (d : ℕ) (hlo : 0 ≤ lo) :
    conj (keyValue L (CellCalculus.cosTuple 0 v G H Pg) (SkeletonKey.pressure n false 0 lo hi t d))
      = keyValue L (CellCalculus.cosTuple 0 v G H Pg) (SkeletonKey.pressure n false 0 lo hi t d) := by
  set x := CellCalculus.cosTuple 0 v G H Pg with hx
  set Q := CellCalculus.harmonicCos 0 Pg with hQ
  have hS := segTest_continuous (keySeg false 0 lo hi t) d
  rw [keyValue_pressure_plane, conj_heightStrip]
  have h1 : (fun p => conj (headPressure L n x p)) = fun p : ℝ × ℝ => presMode L.order (-n) (headPotential Q) p.1 p.2 := by
    funext p
    simp only [headPressure]
    unfold presMode
    exact conj_angle L.order n (fun θ => headPotential Q (cylPoint p.1 θ p.2))
  have h2 : (fun p => conj (L.pressureGradMode n x 2 p)) = L.pressureGradMode (-n) x 2 :=
    (pressureGradMode_neg L x n 2).symm
  rw [h1, h2]
  rcases lt_or_ge lo hi with hlh | hlh
  · by_cases hm : 1 ≤ L.order
    · have hpot : IsPotentialOf Q (headPotential Q) :=
        hShift Q (potentialOf Q) _ (MeshGaugeLinearPotential.potentialOf_spec Q (hPP.harmonic_gradient 0).1)
      exact hPS L.order Q (headPotential Q) hm hpot (hSq Pg hPP 0).1 (hHF Pg hPP hPf 0).1 n lo hi 1 1 (fun r => r) _
        (axisAdmissible_of_nonneg hlo hS) hlh one_pos one_pos continuous_id hS
    · have hm0 : L.order = 0 := by omega
      have e1 : (fun p : ℝ × ℝ => presMode L.order (-n) (headPotential Q) p.1 p.2) = headPressure L n x := by
        funext p
        simp only [headPressure, presMode, hm0, azimuth, Nat.cast_zero, mul_zero]
        rfl
      have e2 : L.pressureGradMode (-n) x 2 = L.pressureGradMode n x 2 := by
        funext p
        simp only [CellLayout.pressureGradMode, modeVec, hm0, azimuth, Nat.cast_zero, mul_zero]
      rw [e1, e2]
  · rw [heightStrip_of_le _ _ _ _ hlh, heightStrip_of_le _ _ _ _ hlh]

end PlanePairInternal

end Breakdown.CertCell

