import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellIndex cellCount weightPoly radialScale heightDeriv heightRatio)

namespace Internal

private theorem le_cellIndex_of_le {l : List ℝ} (hs : l.Pairwise (· < ·)) {k : ℕ} (hk : k + 1 < l.length)
    {t : ℝ} (ht : l[k] ≤ t) : k ≤ cellIndex l t := by
  unfold cellIndex
  have hsub : List.Sublist ((l.drop 1).take k) (l.drop 1).dropLast := by
    rw [List.dropLast_eq_take]
    apply List.take_sublist_take_left
    simp only [List.length_drop]
    omega
  have hall : ∀ x ∈ (l.drop 1).take k, decide (x ≤ t) = true := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_take, List.length_drop] at hj
    simp only [List.getElem_take, List.getElem_drop, decide_eq_true_eq]
    refine le_trans ?_ ht
    rcases Nat.lt_or_ge (1 + j) k with h | h
    · exact le_of_lt (List.pairwise_iff_getElem.1 hs (1 + j) k (by omega) (by omega) h)
    · have he : 1 + j = k := by omega
      simp only [he, le_refl]
  have hfil : ((l.drop 1).take k).filter (fun b => decide (b ≤ t)) = (l.drop 1).take k :=
    List.filter_eq_self.2 hall
  have hle := (hsub.filter (fun b => decide (b ≤ t))).length_le
  rw [hfil] at hle
  have hlen : ((l.drop 1).take k).length = k := by
    simp only [List.length_take, List.length_drop]
    omega
  omega

private theorem le_getD_of_le {l : List ℝ} (hs : l.Pairwise (· < ·)) {k i : ℕ} (hk : k < l.length)
    (hki : k ≤ i) {tb : ℝ} (htb : tb ≤ l[k]) (h1 : tb ≤ 1) : tb ≤ l.getD i 1 := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    rcases Nat.lt_or_ge k i with h | h
    · exact htb.trans (le_of_lt (List.pairwise_iff_getElem.1 hs k i hk hi h))
    · have he : k = i := by omega
      subst he
      exact htb
  · rw [List.getD_eq_default _ _ hi]
    exact h1

private theorem evalHalf_eq_zero_of_break {S : Spline} (hm : IsFullMesh S.mesh) {tb : ℝ} (htb : tb < 1)
    (hv : S.VanishesFrom tb) {b : ℝ} (hb : b ∈ S.mesh.tBreaks) (hbt : tb ≤ b) (hb1 : b < 1) {t : ℝ}
    (ht : b ≤ t) (x : ℝ) : S.evalHalf t x = 0 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hk1 : k + 1 < S.mesh.tBreaks.length := by
    by_contra hcon
    have he : S.mesh.tBreaks.length - 1 = k := by omega
    have hl := hm.t_last
    rw [List.getLast?_eq_getElem?, he, List.getElem?_eq_getElem hk] at hl
    have h1 : S.mesh.tBreaks[k] = 1 := Option.some.inj hl
    linarith
  unfold CellCert.GivenFields.Spline.evalHalf
  rw [hv _ _ (le_getD_of_le hm.t_sorted hk (le_cellIndex_of_le hm.t_sorted hk1 ht) hbt htb.le)]
  simp

private theorem exists_vanish_level {S : Spline} (hm : IsFullMesh S.mesh) {tb : ℝ} (htb : tb < 1)
    (hv : S.VanishesFrom tb) (he : ∃ b ∈ S.mesh.tBreaks, tb ≤ b ∧ b < 1) :
    ∃ c < 1, ∀ t, c ≤ t → ∀ x, S.evalHalf t x = 0 := by
  obtain ⟨b, hb, hbt, hb1⟩ := he
  exact ⟨b, hb1, fun t ht x => evalHalf_eq_zero_of_break hm htb hv hb hbt hb1 ht x⟩

private theorem deriv_zero_of_eventually {f : ℝ → ℂ} {t : ℝ} (h : f =ᶠ[nhds t] fun _ => 0) :
    deriv f t = 0 := by
  rw [h.deriv_eq]
  exact deriv_const t 0

private theorem reducedComps_typeOne_zero (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (hκ : κ.label.1 ≠ 0)
    {c : ℝ} (hr : ∀ t, c ≤ t → ∀ x, A.radial.evalHalf t x = 0)
    (hp : ∀ t, c ≤ t → ∀ x, A.polar.evalHalf t x = 0) {t : ℝ} (ht : c < t) (x : ℝ) :
    reducedComps P κ A t x = 0 := by
  have hur : (fun t' => weightPoly A.lowOrder A.highOrder t' * axisFactor x * A.radial.evalHalf t' x)
      =ᶠ[nhds t] fun _ => 0 :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun t' h => by
      simp only [hr t' (le_of_lt h) x, mul_zero]
  have hθ : (fun x' => polarFactor x' * (weightPoly A.lowOrder A.highOrder t * axisFactor x' *
      A.polar.evalHalf t x')) = fun _ => 0 := by
    funext x'
    simp only [hp t ht.le x', mul_zero]
  have hd1 := deriv_zero_of_eventually hur
  have hd2 : deriv (fun x' => polarFactor x' * (weightPoly A.lowOrder A.highOrder t * axisFactor x' *
      A.polar.evalHalf t x')) x = 0 := by
    rw [hθ]
    exact deriv_const x 0
  simp only [reducedComps, if_neg hκ, shiftedScale, radialScale, heightDeriv, hd1, hd2,
    hr t ht.le x, hp t ht.le x, mul_zero, add_zero, sub_zero]
  funext i
  fin_cases i <;> simp

private theorem reducedComps_typeTwo_zero (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (hκ : κ.label.1 = 0)
    (hax : A.axisCoef = 0) {c : ℝ} (hs : ∀ t, c ≤ t → ∀ x, A.stream.evalHalf t x = 0)
    (hw : ∀ t, c ≤ t → ∀ x, A.swirl.evalHalf t x = 0) {t : ℝ} (ht : c < t) (x : ℝ) :
    reducedComps P κ A t x = 0 := by
  have hsv : ∀ t', c ≤ t' → ∀ x', streamValue P A t' x' = 0 := by
    intro t' h x'
    simp only [streamValue, hax, hs t' h x', zero_mul, add_zero]
  have hst : (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) =ᶠ[nhds t] fun _ => 0 :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun t' h => by
      simp only [hsv t' (le_of_lt h) x, mul_zero]
  have hθ : (fun x' => polarFactor x' * streamValue P A t x') = fun _ => 0 := by
    funext x'
    simp only [hsv t ht.le x', mul_zero]
  have hd1 := deriv_zero_of_eventually hst
  have hd2 : deriv (fun x' => polarFactor x' * streamValue P A t x') x = 0 := by
    rw [hθ]
    exact deriv_const x 0
  simp only [reducedComps, if_pos hκ, shiftedScale, radialScale, heightDeriv, hd1, hd2,
    hsv t ht.le x, hw t ht.le x, mul_zero, add_zero, neg_zero]
  funext i
  fin_cases i <;> simp

private theorem lt_chartCoord_of_radius (P : ShapeParams) (hL : 0 < P.chartLength) {c : ℝ} (hc : c < 1)
    {y : Space} (hy : P.chartLength * c / (1 - c) < ‖y‖) : c < chartCoord P y := by
  unfold chartCoord
  have h1 : 0 < 1 - c := by linarith
  have hd : 0 < ‖y‖ + P.chartLength := by positivity
  rw [lt_div_iff₀ hd]
  rw [div_lt_iff₀ h1] at hy
  nlinarith

private theorem keyVector_vanish_far (P : ShapeParams) (hP : IsShapeParams P) (D : TimeFieldData) (tb : ℝ)
    (hD : IsCompactTimeFieldData tb D) (κ : FieldKey) (hκ : κ ∈ D.keys) :
    ∃ R : ℝ, ∀ σ y, R < ‖y‖ → keyVector P κ (D.amp κ) σ y = 0 := by
  obtain ⟨c, hc1, hc⟩ : ∃ c < 1, ∀ t, c < t → ∀ x, reducedComps P κ (D.amp κ) t x = 0 := by
    by_cases h : κ.label.1 = 0
    · obtain ⟨c1, h1, hs⟩ := exists_vanish_level (hD.field.stream_class κ hκ h).mesh hD.tb_lt
        (hD.typeTwo_vanish κ hκ h).1 (hD.typeTwo_edge κ hκ h).1
      obtain ⟨c2, h2, hw⟩ := exists_vanish_level (hD.field.swirl_class κ hκ h).mesh hD.tb_lt
        (hD.typeTwo_vanish κ hκ h).2 (hD.typeTwo_edge κ hκ h).2
      exact ⟨max c1 c2, max_lt h1 h2, fun t ht x => reducedComps_typeTwo_zero P κ _ h (hD.axisCoef_zero κ hκ h)
        (fun t' h' => hs t' ((le_max_left _ _).trans h')) (fun t' h' => hw t' ((le_max_right _ _).trans h'))
        ht x⟩
    · obtain ⟨c1, h1, hr⟩ := exists_vanish_level (hD.field.radial_class κ hκ h).mesh hD.tb_lt
        (hD.typeOne_vanish κ hκ h).1 (hD.typeOne_edge κ hκ h).1
      obtain ⟨c2, h2, hp⟩ := exists_vanish_level (hD.field.polar_class κ hκ h).mesh hD.tb_lt
        (hD.typeOne_vanish κ hκ h).2 (hD.typeOne_edge κ hκ h).2
      exact ⟨max c1 c2, max_lt h1 h2, fun t ht x => reducedComps_typeOne_zero P κ _ h
        (fun t' h' => hr t' ((le_max_left _ _).trans h')) (fun t' h' => hp t' ((le_max_right _ _).trans h'))
        ht x⟩
  refine ⟨P.chartLength * c / (1 - c), fun σ y hy => ?_⟩
  have hz := hc _ (lt_chartCoord_of_radius P hP.chartLength_pos hc1 hy) (heightRatio y)
  funext i
  simp only [keyVector, hz, Pi.zero_apply, zero_mul, add_zero, mul_zero]

end Internal

theorem compactFieldSupport_holds : CompactFieldSupport := by
  intro P D tb hP hD
  choose! Rf hRf using fun κ (hκ : κ ∈ D.keys) => Internal.keyVector_vanish_far P hP D tb hD κ hκ
  refine ⟨∑ κ ∈ D.keys, |Rf κ|, fun σ y hy => ?_⟩
  have hk : ∀ κ ∈ D.keys, keyVector P κ (D.amp κ) σ y = 0 := fun κ hκ =>
    hRf κ hκ σ y (lt_of_le_of_lt ((le_abs_self _).trans
      (Finset.single_le_sum (fun κ _ => abs_nonneg (Rf κ)) hκ)) hy)
  have hc : complexField P D σ y = 0 := Finset.sum_eq_zero hk
  simp only [shapeInfoField, hc, map_zero]

end GivenShape

end CertCell

end Breakdown
