import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxPinSmooth

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

open CellCert.GivenFields

private theorem sortedFilterGetD (u d b : ℝ) : ∀ I : List ℝ, I.Pairwise (· < ·) → b ∈ I → b ≤ u →
    1 ≤ (I.filter (fun x => decide (x ≤ u))).length ∧
      b ≤ I.getD ((I.filter (fun x => decide (x ≤ u))).length - 1) d := by
  intro I
  induction I with
  | nil => intro _ hb; simp at hb
  | cons x J ih =>
    intro hs hb hbu
    rw [List.pairwise_cons] at hs
    by_cases hx : x ≤ u
    · have hfl : (x :: J).filter (fun x => decide (x ≤ u)) = x :: J.filter (fun x => decide (x ≤ u)) := by
        simp [hx]
      rw [hfl]
      refine ⟨by simp, ?_⟩
      simp only [List.length_cons, Nat.add_sub_cancel]
      rcases List.mem_cons.1 hb with h | h
      · subst h
        rcases Nat.eq_zero_or_pos (J.filter (fun x => decide (x ≤ u))).length with h0 | h0
        · rw [h0]; simp
        · obtain ⟨c, hc⟩ : ∃ c, (J.filter (fun x => decide (x ≤ u))).length = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
          rw [hc]
          simp only [List.getD_cons_succ]
          have hcl : c < J.length := by
            have := List.length_filter_le (fun x => decide (x ≤ u)) J
            omega
          rw [List.getD_eq_getElem _ _ hcl]
          exact (hs.1 _ (List.getElem_mem hcl)).le
      · obtain ⟨h1, h2⟩ := ih hs.2 h hbu
        obtain ⟨c, hc⟩ : ∃ c, (J.filter (fun x => decide (x ≤ u))).length = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
        rw [hc] at h2 ⊢
        simpa using h2
    · exfalso
      rcases List.mem_cons.1 hb with h | h
      · subst h; exact hx hbu
      · exact hx ((hs.1 _ h).le.trans hbu)

private theorem cellIndexGe (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1)
    (tb u : ℝ) (htb : tb ∈ l) (hlt : tb < 1) (hu : tb ≤ u) : tb ≤ l.getD (cellIndex l u) 1 := by
  cases l with
  | nil => simp at h0
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    rw [List.pairwise_cons] at hs
    have hpos : ∀ i, 0 ≤ r.getD i 1 := by
      intro i
      rcases lt_or_ge i r.length with h | h
      · rw [List.getD_eq_getElem _ _ h]; exact (hs.1 _ (List.getElem_mem h)).le
      · rw [List.getD_eq_default _ _ h]; norm_num
    simp only [cellIndex, List.drop_one, List.tail_cons]
    rcases List.mem_cons.1 htb with h | h
    · subst h
      rcases Nat.eq_zero_or_pos ((r.dropLast.filter (fun b => decide (b ≤ u))).length) with hc | hc
      · rw [hc]; simp
      · obtain ⟨c, hc'⟩ : ∃ c, (r.dropLast.filter (fun b => decide (b ≤ u))).length = c + 1 :=
          ⟨_, (Nat.succ_pred_eq_of_pos hc).symm⟩
        rw [hc']
        simpa using hpos c
    · have hr : r ≠ [] := List.ne_nil_of_mem h
      have hlast : r.getLast hr = 1 := by
        have := h1
        rw [List.getLast?_cons, List.getLast?_eq_some_getLast hr] at this
        simpa using this
      have hmem : tb ∈ r.dropLast := by
        have hsplit := List.dropLast_append_getLast hr
        rw [← hsplit] at h
        rcases List.mem_append.1 h with h' | h'
        · exact h'
        · simp at h'; rw [h', hlast] at hlt; exact absurd hlt (lt_irrefl _)
      have hsI : r.dropLast.Pairwise (· < ·) := hs.2.sublist (List.dropLast_sublist r)
      obtain ⟨k1, k2⟩ := sortedFilterGetD u 1 tb r.dropLast hsI hmem hu
      obtain ⟨c, hc'⟩ : ∃ c, (r.dropLast.filter (fun b => decide (b ≤ u))).length = c + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos k1).symm⟩
      rw [hc'] at k2 ⊢
      simp only [List.getD_cons_succ, Nat.add_sub_cancel] at k2 ⊢
      have hcl : c < r.dropLast.length := by
        have := List.length_filter_le (fun b => decide (b ≤ u)) r.dropLast
        omega
      rw [List.getD_eq_getElem _ _ hcl] at k2
      have hcl' : c < r.length := by
        have : r.dropLast.length = r.length - 1 := List.length_dropLast
        omega
      rw [List.getD_eq_getElem _ _ hcl']
      simpa [List.getElem_dropLast] using k2

private theorem splineZero (S : Spline) (hm : IsTensorMesh S.mesh) {tb : ℝ} (hv : S.VanishesFrom tb)
    (hb : tb ∈ S.mesh.tBreaks) (hlt : tb < 1) (odd : Bool) {t : ℝ} (ht : tb ≤ t) (x : ℝ) :
    S.eval odd t x = 0 := by
  simp only [Spline.eval, Spline.evalHalf]
  rw [hv _ _ (cellIndexGe _ hm.t_sorted hm.t_first hm.t_last tb t hb hlt ht)]
  simp

private theorem reducedZero (P : ChartParams) (D : FieldData) (n : ℤ) (β : ℝ) {tb : ℝ}
    (h0 : n = 0 → ∀ t', tb < t' → ∀ x' odd, (D.amp 0).streamAmp.eval odd t' x' = 0 ∧ (D.amp 0).swirlAmp.eval odd t' x' = 0)
    (h1 : n ≠ 0 → ∀ t', tb < t' → ∀ x' odd, (D.amp n).radialAmp.eval odd t' x' = 0 ∧ (D.amp n).polarAmp.eval odd t' x' = 0)
    {t : ℝ} (ht : tb < t) (x : ℝ) : reducedField P D n β t x = 0 := by
  have dz : ∀ f : ℝ → ℝ → ℂ, (∀ t', tb < t' → ∀ x', f t' x' = 0) → deriv (fun t' => f t' x) t = 0 := by
    intro f hf
    have hev : (fun t' => f t' x) =ᶠ[nhds t] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) (fun t' h => hf t' h x)
    rw [hev.deriv_eq]
    simp
  have tw : ∀ (n' : ℤ) (f : ℝ → ℝ → ℂ), (∀ t', tb < t' → ∀ x', f t' x' = 0) → twistedScale P n' β f t x = 0 := by
    intro n' f hf
    simp only [twistedScale, radialScale, dz f hf, hf t ht x]
    simp
  have hd : ∀ f : ℝ → ℝ → ℂ, (∀ t', tb < t' → ∀ x', f t' x' = 0) → heightDeriv f t x = 0 := by
    intro f hf
    have : (fun x' => f t x') = fun _ => (0 : ℂ) := funext (fun x' => hf t ht x')
    simp only [heightDeriv, this]
    simp
  unfold reducedField
  split_ifs with hn
  · have hS := h0 hn
    have e1 : ∀ t', tb < t' → ∀ x', ∀ odd, (D.amp 0).streamAmp.eval odd t' x' = 0 := fun t' h x' o => (hS t' h x' o).1
    have e2 : ∀ t', tb < t' → ∀ x', ∀ odd, (D.amp 0).swirlAmp.eval odd t' x' = 0 := fun t' h x' o => (hS t' h x' o).2
    dsimp only
    rw [tw 0 (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x')
        (fun t' h x' => by simp [e1 t' h x']),
      hd (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x')
        (fun t' h x' => by simp [e1 t' h x'])]
    funext i
    fin_cases i <;> simp [e1 t ht x, e2 t ht x]
  · have hS := h1 hn
    have e1 : ∀ t', tb < t' → ∀ x', ∀ odd, (D.amp n).radialAmp.eval odd t' x' = 0 := fun t' h x' o => (hS t' h x' o).1
    have e2 : ∀ t', tb < t' → ∀ x', ∀ odd, (D.amp n).polarAmp.eval odd t' x' = 0 := fun t' h x' o => (hS t' h x' o).2
    dsimp only
    rw [tw n (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          (D.amp n).radialAmp.eval false t' x') (fun t' h x' => by simp [e1 t' h x']),
      hd (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
          ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x'))
        (fun t' h x' => by simp [e2 t' h x'])]
    funext i
    fin_cases i <;> simp [e1 t ht x, e2 t ht x]

private theorem fieldZero (P : ChartParams) {e : ℕ} {tb : ℝ} (D : FieldData) (hD : IsCompactFieldData P e tb D) (β : ℝ)
    (y : Space) (hy : tb < chartT P y) : fieldOf P D β y = 0 := by
  have hred : ∀ n ∈ D.modes, reducedField P D n β (chartT P y) (heightRatio y) = 0 := by
    intro n hn
    obtain ⟨v1, v2, v3, v4⟩ := hD.vanish n hn
    obtain ⟨b1, b2, b3, b4⟩ := hD.tb_break n hn
    apply reducedZero P D n β (tb := tb) _ _ hy
    · intro h0 t' ht' x' o
      subst h0
      have hc := hD.field.meanStream hn
      have hw := hD.field.meanSwirl hn
      exact ⟨splineZero _ hc.1.mesh v3 b3 hD.tb_lt o ht'.le x', splineZero _ hw.1.mesh v4 b4 hD.tb_lt o ht'.le x'⟩
    · intro h1 t' ht' x' o
      exact ⟨splineZero _ (hD.field.waveRadial n hn h1).mesh v1 b1 hD.tb_lt o ht'.le x',
        splineZero _ (hD.field.wavePolar n hn h1).mesh v2 b2 hD.tb_lt o ht'.le x'⟩
  simp +contextual [fieldOf, hred, ofComponents]
  ext i
  fin_cases i <;> simp

private theorem compactFieldSupport (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ} (D : FieldData)
    (hD : IsCompactFieldData P e tb D) (β : ℝ) : HasCompactSupport (fieldOf P D β) := by
  have h1 : 0 < 1 - tb := by linarith [hD.tb_lt]
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (P.L0 * tb / (1 - tb))) (fun y hy => ?_)
  apply fieldZero P D hD β y
  rw [Metric.mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ h1] at hy
  have hL := hP.L0_pos
  simp only [chartT]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg y]

end FracInternal

namespace CellCert

namespace GivenFields

theorem compactField_regular (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ} (D : FieldData)
    (hD : IsCompactFieldData P e tb D) (β : ℝ) :
    ContDiff ℝ 1 (fieldOf P D β) ∧ HasCompactSupport (fieldOf P D β) ∧
      ∃ K : NNReal, LipschitzWith K (fun y => fderiv ℝ (fieldOf P D β) y) :=
  ⟨(compactField_smooth P hP D hD β).1, FracInternal.compactFieldSupport P hP D hD β,
    (compactField_smooth P hP D hD β).2⟩

end GivenFields

end CellCert

end Breakdown
