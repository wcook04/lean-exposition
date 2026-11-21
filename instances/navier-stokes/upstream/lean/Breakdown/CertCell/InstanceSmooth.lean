import Breakdown.CertCell.InstanceChartGlue

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.GivenFields

namespace SmoothInternal

theorem two_le_length {l : List ℝ} (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) : 2 ≤ l.length := by
  match l, h0, h1 with
  | [], h0, _ => simp at h0
  | [a], h0, h1 =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h0 h1
    rw [h0] at h1
    norm_num at h1
  | a :: b :: r, _, _ => simp

theorem index_lt_count {l : List ℝ} (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) (u : ℝ) :
    cellIndex l u < cellCount l := by
  have h2 := two_le_length h0 h1
  have hle : cellIndex l u ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
  simp only [List.length_dropLast, List.length_drop] at hle
  unfold cellCount
  omega

theorem next_break_le : ∀ (r : List ℝ), r.Pairwise (· < ·) → ∀ {t b : ℝ}, b ∈ r → t < b →
    r.getD (r.dropLast.filter (fun x => decide (x ≤ t))).length 1 ≤ b
  | [], _, _, _, hb, _ => absurd hb List.not_mem_nil
  | [c], _, _, _, hb, _ => by
    rw [List.mem_singleton] at hb
    simp [hb]
  | c :: d :: r, hs, t, b, hb, htb => by
    rw [List.dropLast_cons_cons]
    obtain ⟨hc, hs'⟩ := List.pairwise_cons.1 hs
    by_cases hct : c ≤ t
    · rw [List.filter_cons_of_pos (by simpa using hct), List.length_cons, List.getD_cons_succ]
      have hb' : b ∈ d :: r := by
        rcases List.mem_cons.1 hb with h | h
        · exact absurd (h ▸ hct) (not_le.2 htb)
        · exact h
      exact next_break_le (d :: r) hs' hb' htb
    · have hnil : (c :: (d :: r).dropLast).filter (fun x => decide (x ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        simp only [decide_eq_true_eq, not_le]
        rcases List.mem_cons.1 hx with h | h
        · rw [h]
          exact lt_of_not_ge hct
        · exact lt_trans (lt_of_not_ge hct) (hc x (List.dropLast_subset _ h))
      rw [hnil, List.length_nil, List.getD_cons_zero]
      rcases List.mem_cons.1 hb with h | h
      · exact h.ge
      · exact (hc b h).le

theorem next_break_le_core {l : List ℝ} (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) {t s : ℝ}
    (hs_mem : s ∈ l) (ht0 : 0 ≤ t) (hts : t < s) : l.getD (cellIndex l t + 1) 1 ≤ s := by
  match l, hs, h0, hs_mem with
  | [], _, h0, _ => simp at h0
  | a :: r, hs, h0, hs_mem =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    have hr : s ∈ r := by
      rcases List.mem_cons.1 hs_mem with h | h
      · rw [h, h0] at hts
        exact absurd hts (not_lt.2 ht0)
      · exact h
    unfold cellIndex
    rw [List.drop_one, List.tail_cons, List.getD_cons_succ]
    exact next_break_le r (List.pairwise_cons.1 hs).2 hr hts

theorem chartT_nonneg (P : ChartParams) (hP : IsChartParams P) (y : Space) : 0 ≤ chartT P y :=
  div_nonneg (norm_nonneg y) (add_nonneg (norm_nonneg y) hP.L0_pos.le)

theorem chartT_lt_one (P : ChartParams) (hP : IsChartParams P) (y : Space) : chartT P y < 1 := by
  have hd : 0 < ‖y‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg y) hP.L0_pos
  unfold chartT
  rw [div_lt_one hd]
  linarith [hP.L0_pos]

theorem chartT_pos (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) : 0 < chartT P y :=
  div_pos (norm_pos_iff.2 hy) (add_pos_of_nonneg_of_pos (norm_nonneg y) hP.L0_pos)

theorem chartT_continuous (P : ChartParams) (hP : IsChartParams P) : Continuous (chartT P) :=
  continuous_norm.div (continuous_norm.add continuous_const) fun y =>
    (add_pos_of_nonneg_of_pos (norm_nonneg y) hP.L0_pos).ne'

theorem chartT_zero (P : ChartParams) : chartT P 0 = 0 := by simp [chartT]

theorem pair_contDiffAt (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (fun z : Space => (chartT P z, heightRatio z)) y := by
  have hn : ContDiffAt ℝ 2 (fun z : Space => ‖z‖) y := contDiffAt_norm ℝ hy
  have hc : ContDiffAt ℝ 2 (fun z : Space => z 2) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have h1 : ContDiffAt ℝ 2 (chartT P) y :=
    hn.div (hn.add contDiffAt_const) (add_pos_of_nonneg_of_pos (norm_nonneg y) hP.L0_pos).ne'
  have h2 : ContDiffAt ℝ 2 heightRatio y := hc.div hn (norm_ne_zero_iff.mpr hy)
  exact h1.prodMk h2

theorem core_values (S : ChartScalar) (hS : IsJoinedScalar 2 S) {tStar : ℝ} (hc : IsConstantCore tStar S) :
    ∃ v : ℂ, ∀ t x : ℝ, 0 ≤ t → t < tStar → S.upper.evalHalf t x = v ∧ S.lower.evalHalf t x = v := by
  obtain ⟨-, hmem, v, hv⟩ := hc
  refine ⟨v, fun t x ht0 hts => ?_⟩
  have hm := hS.upper.mesh
  have hml := hS.lower.mesh
  have hi := index_lt_count hm.t_first hm.t_last t
  have hnext := next_break_le_core hm.t_sorted hm.t_first hmem ht0 hts
  obtain ⟨hu, hl⟩ := hv _ hi hnext
  constructor
  · unfold Spline.evalHalf
    rw [hu _ (index_lt_count hm.x_first hm.x_last x), MvPolynomial.eval_C]
  · unfold Spline.evalHalf
    rw [← hS.same_t, hl _ (index_lt_count hml.x_first hml.x_last x), MvPolynomial.eval_C]

end SmoothInternal

open SmoothInternal

theorem scalarSmoothOfJoins : ScalarSmoothOfJoins := by
  intro P S tStar hP hS hc hdec
  have hpos : 0 < tStar := hc.1
  obtain ⟨v, hv⟩ := core_values S hS hc
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have hev : ∀ᶠ z in nhds (0 : Space), chartT P z < tStar := by
      have h := (chartT_continuous P hP).tendsto (0 : Space)
      rw [chartT_zero] at h
      exact h.eventually (gt_mem_nhds hpos)
    have heq : (fun _ : Space => v.re) =ᶠ[nhds 0] S.eval P := by
      filter_upwards [hev] with z hz
      have hz0 := chartT_nonneg P hP z
      simp only [ChartScalar.eval, hdec, pow_zero, one_mul]
      split_ifs
      · rw [(hv _ _ hz0 hz).1]
      · rw [(hv _ _ hz0 hz).2]
    exact contDiffAt_const.congr_of_eventuallyEq heq.symm
  · have hg := chartScalar_halves_contDiffOn S hS
    have hmem : (chartT P y, heightRatio y) ∈ Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) :=
      ⟨⟨chartT_pos P hP hy, chartT_lt_one P hP y⟩, Set.mem_univ _⟩
    have hopen : IsOpen (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
    have hcomp := (hg.contDiffAt (hopen.mem_nhds hmem)).comp y (pair_contDiffAt P hP hy)
    have heq : (fun p : ℝ × ℝ => if 0 ≤ p.2 then (S.upper.evalHalf p.1 p.2).re
        else (S.lower.evalHalf p.1 (-p.2)).re) ∘ (fun z : Space => (chartT P z, heightRatio z))
          =ᶠ[nhds y] S.eval P := by
      filter_upwards [isOpen_ne.mem_nhds hy] with z hz
      have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hiff : 0 ≤ heightRatio z ↔ 0 ≤ z 2 := by
        unfold heightRatio
        exact div_nonneg_iff.trans ⟨fun h => h.elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hnz)),
          fun h => Or.inl ⟨h, hnz.le⟩⟩
      simp only [Function.comp_apply, ChartScalar.eval, hdec, pow_zero, one_mul]
      by_cases h2 : 0 ≤ z 2
      · rw [if_pos (hiff.2 h2), if_pos h2]
      · rw [if_neg (fun h => h2 (hiff.1 h)), if_neg h2]
    exact hcomp.congr_of_eventuallyEq heq.symm

end Instance

end CertCell

end Breakdown
