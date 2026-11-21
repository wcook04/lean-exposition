import Breakdown.CertCell.ShapeSupport

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellIndex weightPoly radialScale heightDeriv heightRatio)

namespace Internal

private theorem take_prefix_inner (l : List ℝ) {k : ℕ} (hk : k + 1 < l.length) :
    ((l.drop 1).take k).Sublist (l.drop 1).dropLast := by
  rw [List.dropLast_eq_take]
  exact List.take_sublist_take_left (by simp only [List.length_drop]; omega)

private theorem index_le_cellIndex {l : List ℝ} (hs : l.Pairwise (· < ·)) {k : ℕ} (hk : k + 1 < l.length)
    {t : ℝ} (ht : l[k] ≤ t) : k ≤ cellIndex l t := by
  have hall : ∀ b ∈ (l.drop 1).take k, decide (b ≤ t) = true := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    simp only [List.length_take, List.length_drop] at hj
    simp only [List.getElem_take, List.getElem_drop, decide_eq_true_eq]
    rcases Nat.lt_or_ge (1 + j) k with h | h
    · exact (List.pairwise_iff_getElem.1 hs (1 + j) k (by omega) (by omega) h).le.trans ht
    · have he : 1 + j = k := by omega
      simpa only [he] using ht
  have hsub := (take_prefix_inner l hk).filter (fun b => decide (b ≤ t))
  rw [List.filter_eq_self.2 hall] at hsub
  have hlen : ((l.drop 1).take k).length = k := by
    simp only [List.length_take, List.length_drop]
    omega
  have h := hsub.length_le
  rw [hlen] at h
  exact h

private theorem break_le_getD {l : List ℝ} (hs : l.Pairwise (· < ·)) {k i : ℕ} (hk : k < l.length)
    (hki : k ≤ i) (h1 : l[k] ≤ 1) : l[k] ≤ l.getD i 1 := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    rcases Nat.lt_or_ge k i with h | h
    · exact (List.pairwise_iff_getElem.1 hs k i hk hi h).le
    · have he : k = i := by omega
      subst he
      exact le_rfl
  · rw [List.getD_eq_default _ _ hi]
    exact h1

private theorem evalHalf_zero_beyond {S : Spline} (hm : IsFullMesh S.mesh) {tb : ℝ} (htb : tb < 1)
    (hv : S.VanishesFrom tb) (hb : tb ∈ S.mesh.tBreaks) {t : ℝ} (ht : tb ≤ t) (x : ℝ) :
    S.evalHalf t x = 0 := by
  obtain ⟨k, hk, hkt⟩ := List.getElem_of_mem hb
  have hk1 : k + 1 < S.mesh.tBreaks.length := by
    by_contra hcon
    have he : S.mesh.tBreaks.length - 1 = k := by omega
    have hl := hm.t_last
    rw [List.getLast?_eq_getElem?, he, List.getElem?_eq_getElem hk, hkt] at hl
    have h1 : tb = 1 := Option.some.inj hl
    linarith
  have hi := index_le_cellIndex hm.t_sorted hk1 (hkt ▸ ht)
  have hle := break_le_getD hm.t_sorted hk hi (hkt ▸ htb.le)
  rw [hkt] at hle
  unfold CellCert.GivenFields.Spline.evalHalf
  rw [hv _ _ hle]
  simp

private theorem deriv_zero_near {f : ℝ → ℂ} {t c : ℝ} (hct : c < t) (h : ∀ s, c < s → f s = 0) :
    deriv f t = 0 := by
  have he : f =ᶠ[nhds t] fun _ => 0 := Filter.eventually_of_mem (Ioi_mem_nhds hct) h
  rw [he.deriv_eq]
  exact deriv_const t 0

private theorem deriv_zero_everywhere {f : ℝ → ℂ} (h : ∀ s, f s = 0) (x : ℝ) : deriv f x = 0 := by
  have he : f = fun _ => 0 := funext h
  rw [he]
  exact deriv_const x 0

private theorem reducedComps_radialPolar_zero (P : ShapeParams) (κ : FieldKey) (A : KeyAmp)
    (hκ : κ.label.1 ≠ 0) {c : ℝ} (hr : ∀ t, c ≤ t → ∀ x, A.radial.evalHalf t x = 0)
    (hp : ∀ t, c ≤ t → ∀ x, A.polar.evalHalf t x = 0) {t : ℝ} (ht : c < t) (x : ℝ) :
    reducedComps P κ A t x = 0 := by
  have hd1 : deriv (fun t' => weightPoly A.lowOrder A.highOrder t' * axisFactor x * A.radial.evalHalf t' x) t
      = 0 := deriv_zero_near ht fun s hs => by simp only [hr s hs.le x, mul_zero]
  have hd2 : deriv (fun x' => polarFactor x' * (weightPoly A.lowOrder A.highOrder t * axisFactor x' *
      A.polar.evalHalf t x')) x = 0 :=
    deriv_zero_everywhere (fun x' => by simp only [hp t ht.le x', mul_zero]) x
  simp only [reducedComps, if_neg hκ, shiftedScale, radialScale, heightDeriv, hd1, hd2,
    hr t ht.le x, hp t ht.le x, mul_zero, add_zero, sub_zero]
  funext i
  fin_cases i <;> simp

private theorem reducedComps_streamSwirl_zero (P : ShapeParams) (κ : FieldKey) (A : KeyAmp)
    (hκ : κ.label.1 = 0) (hax : A.axisCoef = 0) {c : ℝ} (hs : ∀ t, c ≤ t → ∀ x, A.stream.evalHalf t x = 0)
    (hw : ∀ t, c ≤ t → ∀ x, A.swirl.evalHalf t x = 0) {t : ℝ} (ht : c < t) (x : ℝ) :
    reducedComps P κ A t x = 0 := by
  have hv : ∀ t', c ≤ t' → ∀ x', streamValue P A t' x' = 0 := fun t' h x' => by
    simp only [streamValue, hax, hs t' h x', zero_mul, add_zero]
  have hd1 : deriv (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) t = 0 :=
    deriv_zero_near ht fun s h => by simp only [hv s h.le x, mul_zero]
  have hd2 : deriv (fun x' => polarFactor x' * streamValue P A t x') x = 0 :=
    deriv_zero_everywhere (fun x' => by simp only [hv t ht.le x', mul_zero]) x
  simp only [reducedComps, if_pos hκ, shiftedScale, radialScale, heightDeriv, hd1, hd2,
    hv t ht.le x, hw t ht.le x, mul_zero, add_zero, neg_zero]
  funext i
  fin_cases i <;> simp

private theorem edge_lt_chartCoord (P : ShapeParams) (hL : 0 < P.chartLength) {tb : ℝ} (htb : tb < 1)
    {y : Space} (hy : P.chartLength * tb / (1 - tb) < ‖y‖) : tb < chartCoord P y := by
  unfold chartCoord
  have h1 : 0 < 1 - tb := by linarith
  have hd : 0 < ‖y‖ + P.chartLength := by positivity
  rw [lt_div_iff₀ hd]
  rw [div_lt_iff₀ h1] at hy
  nlinarith

private theorem reducedComps_zero_past_edge (P : ShapeParams) (D : TimeFieldData) {tb : ℝ}
    (hD : IsCompactTimeFieldData tb D) (he : HasEdgeBreak tb D) (κ : FieldKey) (hκ : κ ∈ D.keys)
    {t : ℝ} (ht : tb < t) (x : ℝ) : reducedComps P κ (D.amp κ) t x = 0 := by
  by_cases h : κ.label.1 = 0
  · exact reducedComps_streamSwirl_zero P κ _ h (hD.axisCoef_zero κ hκ h)
      (fun t' h' => evalHalf_zero_beyond (hD.field.stream_class κ hκ h).mesh hD.tb_lt
        (hD.typeTwo_vanish κ hκ h).1 ((he κ hκ).2 h).1 h')
      (fun t' h' => evalHalf_zero_beyond (hD.field.swirl_class κ hκ h).mesh hD.tb_lt
        (hD.typeTwo_vanish κ hκ h).2 ((he κ hκ).2 h).2 h') ht x
  · exact reducedComps_radialPolar_zero P κ _ h
      (fun t' h' => evalHalf_zero_beyond (hD.field.radial_class κ hκ h).mesh hD.tb_lt
        (hD.typeOne_vanish κ hκ h).1 ((he κ hκ).1 h).1 h')
      (fun t' h' => evalHalf_zero_beyond (hD.field.polar_class κ hκ h).mesh hD.tb_lt
        (hD.typeOne_vanish κ hκ h).2 ((he κ hκ).1 h).2 h') ht x

end Internal

theorem compactFieldSupportRadius_holds : CompactFieldSupportRadius := by
  intro P D tb hP hD he σ y hy
  have ht := Internal.edge_lt_chartCoord P hP.chartLength_pos hD.tb_lt hy
  have hk : ∀ κ ∈ D.keys, keyVector P κ (D.amp κ) σ y = 0 := by
    intro κ hκ
    have hz := Internal.reducedComps_zero_past_edge P D hD he κ hκ ht (heightRatio y)
    funext i
    simp only [keyVector, hz, Pi.zero_apply, zero_mul, add_zero, mul_zero]
  have hc : complexField P D σ y = 0 := Finset.sum_eq_zero hk
  simp only [shapeInfoField, hc, map_zero]

end GivenShape

end CertCell

end Breakdown
