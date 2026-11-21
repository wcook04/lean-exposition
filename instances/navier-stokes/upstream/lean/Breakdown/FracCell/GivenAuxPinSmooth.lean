import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxActuatorSmooth
import Breakdown.FracCell.GivenAuxPinSmoothLocal

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

open CellCert.GivenFields

private theorem pinSortedFilterGetD (u d b : ℝ) : ∀ I : List ℝ, I.Pairwise (· < ·) → b ∈ I → b ≤ u →
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

private theorem pinCellIndexGe (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1)
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
      obtain ⟨k1, k2⟩ := pinSortedFilterGetD u 1 tb r.dropLast hsI hmem hu
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

private theorem pinSplineZero (S : Spline) (hm : IsTensorMesh S.mesh) {tb : ℝ} (hv : S.VanishesFrom tb)
    (hb : tb ∈ S.mesh.tBreaks) (hlt : tb < 1) (odd : Bool) {t : ℝ} (ht : tb ≤ t) (x : ℝ) :
    S.eval odd t x = 0 := by
  simp only [Spline.eval, Spline.evalHalf]
  rw [hv _ _ (pinCellIndexGe _ hm.t_sorted hm.t_first hm.t_last tb t hb hlt ht)]
  simp

private theorem pinReducedZero (P : ChartParams) (D : FieldData) (n : ℤ) (β : ℝ) {tb : ℝ}
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

private theorem pinFieldZero (P : ChartParams) {e : ℕ} {tb : ℝ} (D : FieldData) (hD : IsCompactFieldData P e tb D) (β : ℝ)
    (y : Space) (hy : tb < chartT P y) : fieldOf P D β y = 0 := by
  have hred : ∀ n ∈ D.modes, reducedField P D n β (chartT P y) (heightRatio y) = 0 := by
    intro n hn
    obtain ⟨v1, v2, v3, v4⟩ := hD.vanish n hn
    obtain ⟨b1, b2, b3, b4⟩ := hD.tb_break n hn
    apply pinReducedZero P D n β (tb := tb) _ _ hy
    · intro h0 t' ht' x' o
      subst h0
      have hc := hD.field.meanStream hn
      have hw := hD.field.meanSwirl hn
      exact ⟨pinSplineZero _ hc.1.mesh v3 b3 hD.tb_lt o ht'.le x', pinSplineZero _ hw.1.mesh v4 b4 hD.tb_lt o ht'.le x'⟩
    · intro h1 t' ht' x' o
      exact ⟨pinSplineZero _ (hD.field.waveRadial n hn h1).mesh v1 b1 hD.tb_lt o ht'.le x',
        pinSplineZero _ (hD.field.wavePolar n hn h1).mesh v2 b2 hD.tb_lt o ht'.le x'⟩
  simp +contextual [fieldOf, hred, ofComponents]
  ext i
  fin_cases i <;> simp


private theorem pinGetDNonneg (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) (i : ℕ) :
    0 ≤ l.getD i 1 := by
  cases l with
  | nil => simp at h0
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    rw [List.pairwise_cons] at hs
    cases i with
    | zero => simp
    | succ k =>
      simp only [List.getD_cons_succ]
      rcases lt_or_ge k r.length with h | h
      · rw [List.getD_eq_getElem _ _ h]; exact (hs.1 _ (List.getElem_mem h)).le
      · rw [List.getD_eq_default _ _ h]; norm_num

private theorem pinSplineAllZero (S : Spline) (hm : IsTensorMesh S.mesh) {tb : ℝ} (hv : S.VanishesFrom tb)
    (htb : tb ≤ 0) (odd : Bool) (t x : ℝ) : S.eval odd t x = 0 := by
  simp only [Spline.eval, Spline.evalHalf]
  rw [hv _ _ (htb.trans (pinGetDNonneg _ hm.t_sorted hm.t_first _))]
  simp

private theorem pinFieldZeroAll (P : ChartParams) {e : ℕ} (D : FieldData) {tb : ℝ} (hD : IsCompactFieldData P e tb D)
    (htb : tb ≤ 0) (β : ℝ) : fieldOf P D β = fun _ => 0 := by
  funext y
  have hred : ∀ n ∈ D.modes, reducedField P D n β (chartT P y) (heightRatio y) = 0 := by
    intro n hn
    obtain ⟨v1, v2, v3, v4⟩ := hD.vanish n hn
    apply pinReducedZero P D n β (tb := chartT P y - 1) _ _ (by linarith)
    · intro h0 t' _ x' o
      subst h0
      exact ⟨pinSplineAllZero _ (hD.field.meanStream hn).1.mesh v3 htb o t' x',
        pinSplineAllZero _ (hD.field.meanSwirl hn).1.mesh v4 htb o t' x'⟩
    · intro h1 t' _ x' o
      exact ⟨pinSplineAllZero _ (hD.field.waveRadial n hn h1).mesh v1 htb o t' x',
        pinSplineAllZero _ (hD.field.wavePolar n hn h1).mesh v2 htb o t' x'⟩
  simp +contextual [fieldOf, hred, ofComponents]
  ext i
  fin_cases i <;> simp

private theorem pinSlopeGlue {E : Type*} [NormedAddCommGroup E] {g : Space → E} {R0 : ℝ} (hR0 : 0 ≤ R0)
    (hz : ∀ y : Space, R0 < ‖y‖ → g y = 0) {C : NNReal}
    (hC : LipschitzOnWith C g (Metric.closedBall 0 (2 * R0 + 1))) :
    ∃ K : NNReal, LipschitzWith K g := by
  refine ⟨C * Real.toNNReal (3 * R0 + 1), LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hK : ((C * Real.toNNReal (3 * R0 + 1) : NNReal) : ℝ) = (C : ℝ) * (3 * R0 + 1) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by linarith)]
  rw [hK]
  have hCn : (0 : ℝ) ≤ C := C.2
  set z : Space := EuclideanSpace.single 0 (2 * R0 + 1) with hzdef
  have hzn : ‖z‖ = 2 * R0 + 1 := by
    rw [hzdef, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hzball : z ∈ Metric.closedBall (0 : Space) (2 * R0 + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right, hzn]
  have hgz : g z = 0 := hz z (by rw [hzn]; linarith)
  have key : ∀ u v : Space, ‖u‖ ≤ R0 → 2 * R0 + 1 < ‖v‖ →
      dist (g u) (g v) ≤ (C : ℝ) * (3 * R0 + 1) * dist u v := by
    intro u v hu hv
    have hgv : g v = 0 := hz v (by linarith)
    have hub : u ∈ Metric.closedBall (0 : Space) (2 * R0 + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    have h1 : dist (g u) (g z) ≤ C * dist u z := hC.dist_le_mul u hub z hzball
    have h2 : dist u z ≤ 3 * R0 + 1 := by
      rw [dist_eq_norm]
      calc ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 3 * R0 + 1 := by rw [hzn]; linarith
    have h3 : 1 ≤ dist u v := by
      rw [dist_eq_norm]
      have := norm_sub_norm_le v u
      rw [norm_sub_rev] at this
      linarith
    rw [hgv, ← hgz]
    calc dist (g u) (g z) ≤ C * dist u z := h1
      _ ≤ C * (3 * R0 + 1) := mul_le_mul_of_nonneg_left h2 hCn
      _ = C * (3 * R0 + 1) * 1 := by ring
      _ ≤ C * (3 * R0 + 1) * dist u v :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hCn (by linarith))
  by_cases hx : ‖x‖ ≤ 2 * R0 + 1
  · by_cases hy : ‖y‖ ≤ 2 * R0 + 1
    · have hxb : x ∈ Metric.closedBall (0 : Space) (2 * R0 + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hx
      have hyb : y ∈ Metric.closedBall (0 : Space) (2 * R0 + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hy
      calc dist (g x) (g y) ≤ C * dist x y := hC.dist_le_mul x hxb y hyb
        _ ≤ C * (3 * R0 + 1) * dist x y := by
          have : (C : ℝ) ≤ C * (3 * R0 + 1) := by nlinarith
          exact mul_le_mul_of_nonneg_right this dist_nonneg
    · rw [not_le] at hy
      by_cases hx0 : ‖x‖ ≤ R0
      · exact key x y hx0 hy
      · rw [not_le] at hx0
        rw [hz x hx0, hz y (by linarith), dist_self]
        exact mul_nonneg (mul_nonneg hCn (by linarith)) dist_nonneg
  · rw [not_le] at hx
    by_cases hy0 : ‖y‖ ≤ R0
    · rw [dist_comm, dist_comm x y]
      exact key y x hy0 hx
    · rw [not_le] at hy0
      rw [hz x (by linarith), hz y hy0, dist_self]
      exact mul_nonneg (mul_nonneg hCn (by linarith)) dist_nonneg

end FracInternal

namespace CellCert

namespace GivenFields

theorem compactField_smooth (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ} (D : FieldData)
    (hD : IsCompactFieldData P e tb D) (β : ℝ) :
    ContDiff ℝ 1 (fieldOf P D β) ∧ ∃ K : NNReal, LipschitzWith K (fun y => fderiv ℝ (fieldOf P D β) y) := by
  by_cases hpos : 0 < tb
  · refine ⟨fieldOf_contDiff_of_compact P hP hD hpos β, ?_⟩
    have h1 : 0 < 1 - tb := by linarith [hD.tb_lt]
    have hL := hP.L0_pos
    set R0 : ℝ := P.L0 * tb / (1 - tb) with hR0
    have hR0n : 0 ≤ R0 := div_nonneg (mul_nonneg hL.le hpos.le) h1.le
    have hz : ∀ y : Space, R0 < ‖y‖ → fderiv ℝ (fieldOf P D β) y = 0 := by
      intro y hy
      have hev : fieldOf P D β =ᶠ[nhds y] fun _ => 0 := by
        have hop : IsOpen {w : Space | R0 < ‖w‖} := isOpen_lt continuous_const continuous_norm
        refine Filter.eventually_of_mem (hop.mem_nhds hy) (fun w hw => ?_)
        apply FracInternal.pinFieldZero P D hD β w
        have hw' : R0 < ‖w‖ := hw
        rw [hR0, div_lt_iff₀ h1] at hw'
        simp only [chartT]
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [norm_nonneg w]
      rw [hev.fderiv_eq]
      simp
    obtain ⟨C, hC⟩ := compactField_fderiv_slopeOn P hP D hD hpos β (2 * R0 + 1)
    exact FracInternal.pinSlopeGlue hR0n hz hC
  · rw [FracInternal.pinFieldZeroAll P D hD (not_lt.1 hpos) β]
    refine ⟨contDiff_const, 0, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp

end GivenFields

end CellCert

end Breakdown
