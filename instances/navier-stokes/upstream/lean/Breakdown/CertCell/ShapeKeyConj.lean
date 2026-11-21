import Breakdown.CertCell.ShapeSplineConj
import Breakdown.CertCell.ShapeSplineAgree

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline radialScale heightDeriv weightPoly)

namespace Internal

theorem conjKey_deriv (f : ℝ → ℂ) (x : ℝ) :
    deriv (fun y => starRingEnd ℂ (f y)) x = starRingEnd ℂ (deriv f x) := by
  change fderiv ℝ (fun y => star (f y)) x 1 = star (fderiv ℝ f x 1)
  rw [fderiv_star]
  rfl

theorem conjKey_radialScale (f : ℝ → ℝ → ℂ) (t x : ℝ) :
    radialScale (fun t' x' => starRingEnd ℂ (f t' x')) t x = starRingEnd ℂ (radialScale f t x) := by
  unfold radialScale
  rw [conjKey_deriv (fun t' => f t' x) t, map_mul, Complex.conj_ofReal]

theorem conjKey_heightDeriv (f : ℝ → ℝ → ℂ) (t x : ℝ) :
    heightDeriv (fun t' x' => starRingEnd ℂ (f t' x')) t x = starRingEnd ℂ (heightDeriv f t x) :=
  conjKey_deriv (fun x' => f t x') x

theorem conjKey_shiftedScale (P : ShapeParams) (j : ℤ) (f : ℝ → ℝ → ℂ) (t x : ℝ) :
    shiftedScale P (-j) (fun t' x' => starRingEnd ℂ (f t' x')) t x =
      starRingEnd ℂ (shiftedScale P j f t x) := by
  unfold shiftedScale
  rw [conjKey_radialScale]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem conjKey_weightPoly (a b : ℕ) (t : ℝ) : starRingEnd ℂ (weightPoly a b t) = weightPoly a b t := by
  unfold weightPoly
  exact Complex.conj_ofReal _

theorem conjKey_labelTime (ι : ℤ × ℤ) : labelTime (-ι) = -labelTime ι := by
  unfold labelTime
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

theorem conjKey_labelAzimuth (m : ℕ) (ι : ℤ × ℤ) : labelAzimuth m (-ι) = -labelAzimuth m ι := by
  unfold labelAzimuth
  simp only [Prod.fst_neg]
  ring

theorem conjKey_keyPhase (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (y : Space) :
    keyPhase P κ.negKey σ y = starRingEnd ℂ (keyPhase P κ σ y) := by
  unfold keyPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [FieldKey.negKey, conjKey_labelTime, conjKey_labelAzimuth, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring

theorem conjKey_evalHalf (S : Spline) (t x : ℝ) :
    S.conj.evalHalf t x = starRingEnd ℂ (S.evalHalf t x) :=
  eval_real_map_conj t x _

theorem conjKey_reducedComps (P : ShapeParams) (κ : FieldKey) (A B : KeyAmp)
    (h1 : κ.label.1 ≠ 0 → (∀ t x, B.radial.evalHalf t x = starRingEnd ℂ (A.radial.evalHalf t x)) ∧
      (∀ t x, B.polar.evalHalf t x = starRingEnd ℂ (A.polar.evalHalf t x)) ∧ B.lowOrder = A.lowOrder)
    (h2 : κ.label.1 = 0 → (∀ t x, B.stream.evalHalf t x = starRingEnd ℂ (A.stream.evalHalf t x)) ∧
      (∀ t x, B.swirl.evalHalf t x = starRingEnd ℂ (A.swirl.evalHalf t x)) ∧
        B.axisCoef = starRingEnd ℂ A.axisCoef)
    (hh : B.highOrder = A.highOrder) (t x : ℝ) :
    reducedComps P κ.negKey B t x = fun i => starRingEnd ℂ (reducedComps P κ A t x i) := by
  have hlab : κ.negKey.label.1 = -κ.label.1 := rfl
  have hj : κ.negKey.phaseIndex = -κ.phaseIndex := rfl
  by_cases h0 : κ.label.1 = 0
  · obtain ⟨hs, hw, ha⟩ := h2 h0
    have hn : κ.negKey.label.1 = 0 := by rw [hlab, h0, neg_zero]
    have hsv : ∀ t' x', streamValue P B t' x' = starRingEnd ℂ (streamValue P A t' x') := by
      intro t' x'
      simp only [streamValue, hs, ha, map_add, map_mul, Complex.conj_ofReal]
    have hq : (fun t' x' => polarFactor x' * streamValue P B t' x') =
        fun t' x' => starRingEnd ℂ (polarFactor x' * streamValue P A t' x') := by
      funext t' x'
      rw [hsv, map_mul]
      unfold polarFactor
      rw [Complex.conj_ofReal]
    have hp : (fun t' x' => weightPoly 1 B.highOrder t' * streamValue P B t' x') =
        fun t' x' => starRingEnd ℂ (weightPoly 1 A.highOrder t' * streamValue P A t' x') := by
      funext t' x'
      rw [hsv, map_mul, conjKey_weightPoly, hh]
    funext i
    simp only [reducedComps, if_pos h0, if_pos hn]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hq, conjKey_heightDeriv, hh, map_neg, map_mul, conjKey_weightPoly]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hp, hj, conjKey_shiftedScale, hsv, hh, map_neg, map_add, map_mul, map_mul, conjKey_weightPoly,
        map_ofNat]
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [hw, hh, map_mul, conjKey_weightPoly]
  · obtain ⟨hr, hpo, hl⟩ := h1 h0
    have hn : ¬ κ.negKey.label.1 = 0 := by rw [hlab]; exact neg_ne_zero.mpr h0
    have hur : (fun t' x' => weightPoly B.lowOrder B.highOrder t' * axisFactor x' * B.radial.evalHalf t' x') =
        fun t' x' => starRingEnd ℂ (weightPoly A.lowOrder A.highOrder t' * axisFactor x' *
          A.radial.evalHalf t' x') := by
      funext t' x'
      rw [hr, hl, hh, map_mul, map_mul, conjKey_weightPoly]
      unfold axisFactor
      rw [Complex.conj_ofReal]
    have hut : (fun t' x' => polarFactor x' *
        (weightPoly B.lowOrder B.highOrder t' * axisFactor x' * B.polar.evalHalf t' x')) =
        fun t' x' => starRingEnd ℂ (polarFactor x' *
          (weightPoly A.lowOrder A.highOrder t' * axisFactor x' * A.polar.evalHalf t' x')) := by
      funext t' x'
      rw [hpo, hl, hh, map_mul, map_mul, map_mul, conjKey_weightPoly]
      unfold axisFactor polarFactor
      rw [Complex.conj_ofReal, Complex.conj_ofReal]
    have hk : (labelAzimuth P.azimuthOrder κ.negKey.label : ℂ) =
        -(labelAzimuth P.azimuthOrder κ.label : ℂ) := by
      rw [show κ.negKey.label = -κ.label from rfl, conjKey_labelAzimuth]
      push_cast
      ring
    funext i
    simp only [reducedComps, if_neg h0, if_neg hn]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact congrFun (congrFun hur t) x
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hpo, hl, hh, map_mul, map_mul, conjKey_weightPoly]
      unfold axisFactor
      rw [Complex.conj_ofReal]
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [hur, hut, hj, conjKey_shiftedScale, conjKey_heightDeriv, hk]
      have hur' := congrFun (congrFun hur t) x
      rw [hur']
      simp only [map_mul, map_sub, map_add, map_div₀, Complex.conj_I, map_intCast, map_ofNat]
      ring

end Internal

open Internal in
theorem keyConjugate : KeyConjugate := by
  intro P D κ σ y hD hκ
  have hnκ : κ.negKey ∈ D.keys := (hD.keys_neg κ).1 hκ
  have hlab : κ.negKey.label.1 = -κ.label.1 := rfl
  have h1 : κ.label.1 ≠ 0 →
      (∀ t x, (D.amp κ.negKey).radial.evalHalf t x = starRingEnd ℂ ((D.amp κ).radial.evalHalf t x)) ∧
      (∀ t x, (D.amp κ.negKey).polar.evalHalf t x = starRingEnd ℂ ((D.amp κ).polar.evalHalf t x)) ∧
        (D.amp κ.negKey).lowOrder = (D.amp κ).lowOrder := by
    intro h0
    have hn : κ.negKey.label.1 ≠ 0 := by rw [hlab]; exact neg_ne_zero.mpr h0
    refine ⟨fun t x => ?_, fun t x => ?_, (hD.neg_orders κ hκ).1⟩
    · rw [evalHalf_of_agrees (hD.neg_radial κ hκ h0) (hD.radial_class _ hnκ hn).mesh, conjKey_evalHalf]
    · rw [evalHalf_of_agrees (hD.neg_polar κ hκ h0) (hD.polar_class _ hnκ hn).mesh, conjKey_evalHalf]
  have h2 : κ.label.1 = 0 →
      (∀ t x, (D.amp κ.negKey).stream.evalHalf t x = starRingEnd ℂ ((D.amp κ).stream.evalHalf t x)) ∧
      (∀ t x, (D.amp κ.negKey).swirl.evalHalf t x = starRingEnd ℂ ((D.amp κ).swirl.evalHalf t x)) ∧
        (D.amp κ.negKey).axisCoef = starRingEnd ℂ (D.amp κ).axisCoef := by
    intro h0
    have hn : κ.negKey.label.1 = 0 := by rw [hlab, h0, neg_zero]
    refine ⟨fun t x => ?_, fun t x => ?_, hD.neg_axisCoef κ hκ h0⟩
    · rw [evalHalf_of_agrees (hD.neg_stream κ hκ h0) (hD.stream_class _ hnκ hn).mesh, conjKey_evalHalf]
    · rw [evalHalf_of_agrees (hD.neg_swirl κ hκ h0) (hD.swirl_class _ hnκ hn).mesh, conjKey_evalHalf]
  have hc := conjKey_reducedComps P κ (D.amp κ) (D.amp κ.negKey) h1 h2 (hD.neg_orders κ hκ).2
  funext i
  simp only [keyVector, conjKey_keyPhase, hc, map_mul, map_add, Complex.conj_ofReal]

end GivenShape

end CertCell

end Breakdown
