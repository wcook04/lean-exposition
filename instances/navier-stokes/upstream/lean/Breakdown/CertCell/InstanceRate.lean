import Breakdown.CertCell.InstanceSlope

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.GivenFields

namespace Internal.Rate

theorem height_abs_le (y : Space) : |heightRatio y| ≤ 1 := by
  unfold heightRatio
  rcases eq_or_lt_of_le (norm_nonneg y) with h | h
  · rw [← h]
    simp
  · rw [abs_div, abs_norm, div_le_one h]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 2

theorem chart_mem_unit (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    chartT P y ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : 0 < ‖y‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg y) hP.L0_pos
  unfold chartT
  exact ⟨div_nonneg (norm_nonneg _) hd.le, (div_le_one hd).2 (by linarith [hP.L0_pos])⟩

theorem norm_mul_one_sub_chart (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    ‖y‖ * (1 - chartT P y) ≤ P.L0 := by
  have hL := hP.L0_pos
  have hd : 0 < ‖y‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg y) hL
  have e : 1 - chartT P y = P.L0 / (‖y‖ + P.L0) := by
    unfold chartT
    field_simp
    ring
  rw [e, ← mul_div_assoc, div_le_iff₀ hd]
  nlinarith [norm_nonneg y]

theorem norm_mul_chart_sub (P : ChartParams) (hP : IsChartParams P) (y x : Space) :
    ‖y‖ * |chartT P x - chartT P y| ≤ ‖x - y‖ := by
  have hL := hP.L0_pos
  have hy : 0 < ‖y‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg y) hL
  have hx : 0 < ‖x‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg x) hL
  have e : chartT P x - chartT P y = P.L0 * (‖x‖ - ‖y‖) / ((‖x‖ + P.L0) * (‖y‖ + P.L0)) := by
    unfold chartT
    rw [div_sub_div _ _ hx.ne' hy.ne']
    congr 1
    ring
  have h1 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h2 : ‖y‖ * P.L0 ≤ (‖x‖ + P.L0) * (‖y‖ + P.L0) := by
    nlinarith [norm_nonneg x, norm_nonneg y]
  rw [e, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (mul_pos hx hy), ← mul_div_assoc,
    div_le_iff₀ (mul_pos hx hy)]
  calc ‖y‖ * (P.L0 * |‖x‖ - ‖y‖|) = (‖y‖ * P.L0) * |‖x‖ - ‖y‖| := by ring
    _ ≤ ((‖x‖ + P.L0) * (‖y‖ + P.L0)) * ‖x - y‖ := mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    _ = ‖x - y‖ * ((‖x‖ + P.L0) * (‖y‖ + P.L0)) := by ring

theorem one_sub_pow_sub_le (d : ℕ) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |(1 - a) ^ d - (1 - b) ^ d| ≤ d * |a - b| := by
  have h := abs_pow_sub_pow_le (a := 1 - a) (b := 1 - b) (n := d)
  have hm : max |1 - a| |1 - b| ^ (d - 1) ≤ 1 := by
    apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
    refine max_le ?_ ?_
    · rw [abs_of_nonneg (by linarith [ha.2])]
      linarith [ha.1]
    · rw [abs_of_nonneg (by linarith [hb.2])]
      linarith [hb.1]
  rw [show (1 - a) - (1 - b) = -(a - b) by ring, abs_neg] at h
  calc _ ≤ |a - b| * d * max |1 - a| |1 - b| ^ (d - 1) := h
    _ ≤ |a - b| * d * 1 := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = d * |a - b| := by ring

theorem one_sub_pow_abs_le (d : ℕ) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) : |(1 - a) ^ d| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg (by linarith [ha.2]) _)]
  exact pow_le_one₀ (by linarith [ha.2]) (by linarith [ha.1])

end Internal.Rate

open Internal.Slope Internal.Rate in
theorem scalarRateOfDecay (hlip : ScalarSlopeBoundOfJoins) : ScalarRateOfDecay := by
  intro P S hP hS hF
  obtain ⟨v, hvu, hvl⟩ := hF
  obtain ⟨A, hA0, hA⟩ := half_t_bound S hS
  obtain ⟨C, hC0, hC⟩ := half_x_bound S hS v hvu hvl
  obtain ⟨B, hB0, hB⟩ := half_bound S A C hA hC hA0
  have hL := hP.L0_pos
  have ev : ∀ z, S.eval P z = (1 - chartT P z) ^ S.decay * halfVal S (chartT P z) (heightRatio z) :=
    fun z => congrFun (eval_eq P S) z
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = S.decay * B + A + 2 * C := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    positivity
  refine ⟨max B (max (P.L0 ^ S.decay * B) M), fun y => ⟨?_, ?_, ?_⟩⟩
  · have ht := chart_mem_unit P hP y
    refine le_max_of_le_left ?_
    rw [ev, abs_mul]
    calc _ ≤ 1 * B := mul_le_mul (one_sub_pow_abs_le _ ht) (hB _ ht _ (height_abs_le y)) (abs_nonneg _)
          zero_le_one
      _ = B := one_mul B
  · have ht := chart_mem_unit P hP y
    have h0 : 0 ≤ 1 - chartT P y := by linarith [ht.2]
    have h1 : ‖y‖ ^ S.decay * |(1 - chartT P y) ^ S.decay| ≤ P.L0 ^ S.decay := by
      rw [abs_of_nonneg (pow_nonneg h0 _), ← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) h0) (norm_mul_one_sub_chart P hP y) _
    refine le_max_of_le_right (le_max_of_le_left ?_)
    rw [ev, abs_mul, ← mul_assoc]
    exact mul_le_mul h1 (hB _ ht _ (height_abs_le y)) (abs_nonneg _) (by positivity)
  · refine le_max_of_le_right (le_max_of_le_right ?_)
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | hy
    · rw [← h0, zero_mul]
      exact hM0
    · have key : ∀ x, ‖S.eval P x - S.eval P y‖ ≤ M / ‖y‖ * ‖x - y‖ := by
        intro x
        rw [ev, ev, Real.norm_eq_abs]
        have ha := chart_mem_unit P hP x
        have hb := chart_mem_unit P hP y
        have hu := height_abs_le x
        have hw := height_abs_le y
        have e1 : (1 - chartT P x) ^ S.decay * halfVal S (chartT P x) (heightRatio x) -
            (1 - chartT P y) ^ S.decay * halfVal S (chartT P y) (heightRatio y) =
            ((1 - chartT P x) ^ S.decay - (1 - chartT P y) ^ S.decay) *
                halfVal S (chartT P x) (heightRatio x) +
              (1 - chartT P y) ^ S.decay *
                ((halfVal S (chartT P x) (heightRatio x) - halfVal S (chartT P y) (heightRatio x)) +
                  (halfVal S (chartT P y) (heightRatio x) - halfVal S (chartT P y) (heightRatio y))) := by
          ring
        have p5 : |halfVal S (chartT P y) (heightRatio x) - halfVal S (chartT P y) (heightRatio y)| ≤
            C * |heightRatio x - heightRatio y| := by
          refine (hC _ hb _ _ hu hw).trans ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) hb.2) hC0
        have q1 : |chartT P x - chartT P y| ≤ ‖x - y‖ / ‖y‖ := by
          rw [le_div_iff₀ hy]
          linarith [norm_mul_chart_sub P hP y x]
        have q2 : |heightRatio x - heightRatio y| ≤ 2 * ‖x - y‖ / ‖y‖ := by
          rw [le_div_iff₀ hy]
          linarith [height_slope x y]
        have s1 : |((1 - chartT P x) ^ S.decay - (1 - chartT P y) ^ S.decay) *
            halfVal S (chartT P x) (heightRatio x)| ≤ S.decay * |chartT P x - chartT P y| * B := by
          rw [abs_mul]
          exact mul_le_mul (one_sub_pow_sub_le S.decay ha hb) (hB _ ha _ hu) (abs_nonneg _) (by positivity)
        have s2 : |(1 - chartT P y) ^ S.decay *
            ((halfVal S (chartT P x) (heightRatio x) - halfVal S (chartT P y) (heightRatio x)) +
              (halfVal S (chartT P y) (heightRatio x) - halfVal S (chartT P y) (heightRatio y)))| ≤
            A * |chartT P x - chartT P y| + C * |heightRatio x - heightRatio y| := by
          rw [abs_mul]
          calc _ ≤ 1 * (A * |chartT P x - chartT P y| + C * |heightRatio x - heightRatio y|) :=
                mul_le_mul (one_sub_pow_abs_le _ hb)
                  ((abs_add_le _ _).trans (add_le_add (hA _ hu _ ha _ hb) p5)) (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        have s3 := abs_add_le (((1 - chartT P x) ^ S.decay - (1 - chartT P y) ^ S.decay) *
            halfVal S (chartT P x) (heightRatio x))
          ((1 - chartT P y) ^ S.decay *
            ((halfVal S (chartT P x) (heightRatio x) - halfVal S (chartT P y) (heightRatio x)) +
              (halfVal S (chartT P y) (heightRatio x) - halfVal S (chartT P y) (heightRatio y))))
        have r1 : S.decay * |chartT P x - chartT P y| * B ≤ S.decay * B * (‖x - y‖ / ‖y‖) := by
          calc S.decay * |chartT P x - chartT P y| * B = (S.decay * B) * |chartT P x - chartT P y| := by ring
            _ ≤ (S.decay * B) * (‖x - y‖ / ‖y‖) := mul_le_mul_of_nonneg_left q1 (by positivity)
        have r2 : A * |chartT P x - chartT P y| ≤ A * (‖x - y‖ / ‖y‖) := mul_le_mul_of_nonneg_left q1 hA0
        have r3 : C * |heightRatio x - heightRatio y| ≤ C * (2 * ‖x - y‖ / ‖y‖) :=
          mul_le_mul_of_nonneg_left q2 hC0
        have eM : M / ‖y‖ * ‖x - y‖ =
            S.decay * B * (‖x - y‖ / ‖y‖) + A * (‖x - y‖ / ‖y‖) + C * (2 * ‖x - y‖ / ‖y‖) := by
          rw [hM]
          ring
        rw [e1, eM]
        linarith
      have hd := norm_fderiv_le_of_lip' ℝ (div_nonneg hM0 hy.le) (Filter.Eventually.of_forall key)
      unfold PieceWeights.wtGrad
      calc ‖y‖ * ‖fderiv ℝ (S.eval P) y‖ ≤ ‖y‖ * (M / ‖y‖) := mul_le_mul_of_nonneg_left hd hy.le
        _ = M := by field_simp

end Instance

end CertCell

end Breakdown
