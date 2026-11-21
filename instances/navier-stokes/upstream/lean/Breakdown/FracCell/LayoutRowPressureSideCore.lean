import Breakdown.FracCell.SegmentIndependenceParts

open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.LayoutRowPressureSideCore

open CellCert CellCert.CellFormula CellCert.CellAnalysis

private theorem tent_right_cell {l m u x w : ℝ} (hw : 0 < w) (hml : m - l = w) (hum : u - m = w)
    (hx1 : m < x) (hx2 : x < u) :
    CornerParts.tentFn l m u x = (u - x) / w ∧ CornerParts.tentSlope l m u x = -(1 / w) := by
  constructor
  · unfold CornerParts.tentFn
    rw [hml, hum]
    have h1 : (u - x) / w ≤ (x - l) / w := (div_le_div_iff_of_pos_right hw).2 (by linarith)
    rw [min_eq_right h1, max_eq_right (div_nonneg (by linarith) hw.le)]
  · unfold CornerParts.tentSlope
    rw [if_pos (show x ∈ Icc l u from ⟨by linarith, by linarith⟩), if_neg (not_le.2 hx1),
      show m - u = -w by linarith, div_neg]

private theorem tent_left_cell {l m u x w : ℝ} (hw : 0 < w) (hml : m - l = w) (hum : u - m = w)
    (hx1 : l < x) (hx2 : x < m) :
    CornerParts.tentFn l m u x = (x - l) / w ∧ CornerParts.tentSlope l m u x = 1 / w := by
  constructor
  · unfold CornerParts.tentFn
    rw [hml, hum]
    have h1 : (x - l) / w ≤ (u - x) / w := (div_le_div_iff_of_pos_right hw).2 (by linarith)
    rw [min_eq_left h1, max_eq_right (div_nonneg (by linarith) hw.le)]
  · unfold CornerParts.tentSlope
    rw [if_pos (show x ∈ Icc l u from ⟨by linarith, by linarith⟩), if_pos hx2.le, hml]

private theorem tent_outside {l m u x : ℝ} (hlm : l < m) (hmu : m < u) (hx : x ∉ Icc l u) :
    CornerParts.tentFn l m u x = 0 ∧ CornerParts.tentSlope l m u x = 0 := by
  refine ⟨?_, by unfold CornerParts.tentSlope; rw [if_neg hx]⟩
  unfold CornerParts.tentFn
  apply max_eq_left
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact (min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  · exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

private theorem tent_le_ramp {l m u x : ℝ} (hl : 0 ≤ l) (hlm : l < m) (hmu : m < u) (hx : 0 ≤ x) :
    CornerParts.tentFn l m u x ≤ x / (m - l) := by
  unfold CornerParts.tentFn
  apply max_le (div_nonneg hx (by linarith))
  rcases le_or_gt x m with h | h
  · exact (min_le_left _ _).trans ((div_le_div_iff_of_pos_right (by linarith)).2 (by linarith))
  · refine (min_le_right _ _).trans ?_
    have h1 : (u - x) / (u - m) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : 1 ≤ x / (m - l) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith

private theorem tent_le_one {l m u x : ℝ} (hlm : l < m) (hmu : m < u) :
    CornerParts.tentFn l m u x ≤ 1 := by
  unfold CornerParts.tentFn
  apply max_le zero_le_one
  rcases le_or_gt x m with h | h
  · exact (min_le_left _ _).trans (by rw [div_le_one (by linarith)]; linarith)
  · exact (min_le_right _ _).trans (by rw [div_le_one (by linarith)]; linarith)

private theorem tent_nonneg (l m u x : ℝ) : 0 ≤ CornerParts.tentFn l m u x := by
  unfold CornerParts.tentFn; exact le_max_left _ _

private theorem tent_at_zero {l m u : ℝ} (hl : 0 ≤ l) (hlm : l < m) (hmu : m < u) :
    CornerParts.tentFn l m u 0 = 0 :=
  le_antisymm (by have := tent_le_ramp hl hlm hmu le_rfl; rwa [zero_div] at this) (tent_nonneg _ _ _ _)

private theorem slope_abs_le {l m u x : ℝ} (hlm : l < m) (hmu : m < u) :
    |CornerParts.tentSlope l m u x| ≤ 1 / (m - l) + 1 / (u - m) := by
  have h1 : 0 < 1 / (m - l) := one_div_pos.2 (sub_pos.2 hlm)
  have h2 : 0 < 1 / (u - m) := one_div_pos.2 (sub_pos.2 hmu)
  unfold CornerParts.tentSlope
  split_ifs with hx hy
  · rw [abs_of_pos h1]; linarith
  · rw [show m - u = -(u - m) by ring, div_neg, abs_neg, abs_of_pos h2]; linarith
  · rw [abs_zero]; linarith

private theorem slope_meas (l m u : ℝ) : Measurable (CornerParts.tentSlope l m u) := by
  unfold CornerParts.tentSlope
  refine Measurable.ite measurableSet_Icc ?_ measurable_const
  exact measurable_const.div (measurable_const.sub (Measurable.ite measurableSet_Iic measurable_const measurable_const))

private theorem tent_cont (l m u : ℝ) : Continuous (CornerParts.tentFn l m u) := by
  unfold CornerParts.tentFn
  exact continuous_const.max (((continuous_id.sub continuous_const).div_const _).min
    ((continuous_const.sub continuous_id).div_const _))

private theorem icc_sub_sym (a b : ℝ) : Icc a b ⊆ Icc (-(|a| + |b|)) (|a| + |b|) := by
  intro s hs
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, hs.1]
  · linarith [le_abs_self b, abs_nonneg a, hs.2]

private theorem null_fst_set {T : Set ℝ} (hT : T.Countable) : (volume : Measure (ℝ × ℝ)) (T ×ˢ univ) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, hT.measure_zero, zero_mul]

private theorem null_snd_set {T : Set ℝ} (hT : T.Countable) : (volume : Measure (ℝ × ℝ)) (univ ×ˢ T) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, hT.measure_zero, mul_zero]

private theorem ae_diff_fst {G : ℝ × ℝ → ℂ} {C : NNReal} (hG : LipschitzWith C G) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun r => G (r, p.2)) p.1 := by
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun r => G (r, x.2)) x.1} := by
    have h0 := measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun z r => G (r, z))
      (hG.continuous.comp continuous_swap)
    exact measurable_swap h0
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas, Measure.ae_ae_comm hmeas]
  refine Filter.Eventually.of_forall fun z => ?_
  have hl : LipschitzWith (C * 1) (fun r => G (r, z)) := hG.comp (LipschitzWith.prodMk_right z)
  exact hl.ae_differentiableAt_real

private theorem ae_diff_snd {G : ℝ × ℝ → ℂ} {C : NNReal} (hG : LipschitzWith C G) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun z => G (p.1, z)) p.2 := by
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun z => G (x.1, z)) x.2} :=
    measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun r z => G (r, z)) hG.continuous
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
  refine Filter.Eventually.of_forall fun r => ?_
  have hl : LipschitzWith (C * 1) (fun z => G (r, z)) := hG.comp (LipschitzWith.prodMk_left r)
  exact hl.ae_differentiableAt_real

private theorem grid_cell {a x s : ℝ} (hs : 0 < s) {n : ℕ} (hx1 : a < x) (hx2 : x < a + (n : ℝ) * s)
    (hG : ∀ k : ℕ, x ≠ a + (k : ℝ) * s) :
    ∃ j : ℕ, j + 1 ≤ n ∧ a + (j : ℝ) * s < x ∧ x < a + ((j : ℝ) + 1) * s := by
  have ht0 : 0 ≤ (x - a) / s := div_nonneg (by linarith) hs.le
  refine ⟨⌊(x - a) / s⌋₊, ?_, ?_, ?_⟩
  · have h1 : (x - a) / s < n := by rw [div_lt_iff₀ hs]; linarith
    have h2 := (Nat.floor_lt ht0).2 h1
    omega
  · have hle : (⌊(x - a) / s⌋₊ : ℝ) ≤ (x - a) / s := Nat.floor_le ht0
    have hle' : a + (⌊(x - a) / s⌋₊ : ℝ) * s ≤ x := by
      have := mul_le_mul_of_nonneg_right hle hs.le
      rw [div_mul_cancel₀ _ hs.ne'] at this; linarith
    exact lt_of_le_of_ne hle' (fun e => hG _ e.symm)
  · have h3 := Nat.lt_floor_add_one ((x - a) / s)
    have := mul_lt_mul_of_pos_right h3 hs
    rw [div_mul_cancel₀ _ hs.ne'] at this; linarith

private theorem grid_sum (f : ℝ → ℂ) (α β : ℂ) {a s x : ℝ} (hs : 0 < s) {n j : ℕ} (hj : j + 1 ≤ n)
    (h1 : a + (j : ℝ) * s < x) (h2 : x < a + ((j : ℝ) + 1) * s) :
    ∑ k ∈ Finset.range (n + 1), f (a + (k : ℝ) * s) *
      (((CornerParts.tentSlope (a + ((k : ℝ) - 1) * s) (a + (k : ℝ) * s) (a + ((k : ℝ) + 1) * s) x : ℝ) : ℂ) * α +
        ((CornerParts.tentFn (a + ((k : ℝ) - 1) * s) (a + (k : ℝ) * s) (a + ((k : ℝ) + 1) * s) x : ℝ) : ℂ) * β) =
      β * ((((a + ((j : ℝ) + 1) * s - x) / s : ℝ) : ℂ) * f (a + (j : ℝ) * s) +
          (((x - (a + (j : ℝ) * s)) / s : ℝ) : ℂ) * f (a + ((j : ℝ) + 1) * s)) +
        α * ((((1 / s) : ℝ) : ℂ) * (f (a + ((j : ℝ) + 1) * s) - f (a + (j : ℝ) * s))) := by
  rw [Finset.sum_eq_add j (j + 1) (by omega) ?_ ?_ ?_]
  · obtain ⟨e1, e2⟩ := tent_right_cell (l := a + ((j : ℝ) - 1) * s) (m := a + (j : ℝ) * s)
      (u := a + ((j : ℝ) + 1) * s) hs (by ring) (by ring) h1 h2
    have c1 : a + (((j + 1 : ℕ) : ℝ) - 1) * s = a + (j : ℝ) * s := by push_cast; ring
    have c2 : a + ((j + 1 : ℕ) : ℝ) * s = a + ((j : ℝ) + 1) * s := by push_cast; ring
    have c3 : a + (((j + 1 : ℕ) : ℝ) + 1) * s = a + ((j : ℝ) + 2) * s := by push_cast; ring
    rw [c1, c2, c3]
    obtain ⟨e3, e4⟩ := tent_left_cell (l := a + (j : ℝ) * s) (m := a + ((j : ℝ) + 1) * s)
      (u := a + ((j : ℝ) + 2) * s) hs (by ring) (by ring) h1 h2
    rw [e1, e2, e3, e4]
    push_cast
    ring
  · intro k _ hk
    have hx : x ∉ Icc (a + ((k : ℝ) - 1) * s) (a + ((k : ℝ) + 1) * s) := by
      rintro ⟨hx1, hx2⟩
      rcases lt_or_gt_of_ne hk.1 with hkj | hkj
      · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hkj
        nlinarith
      · have : (j : ℝ) + 2 ≤ k := by exact_mod_cast (show j + 2 ≤ k by omega)
        nlinarith
    obtain ⟨e1, e2⟩ := tent_outside (m := a + (k : ℝ) * s) (by linarith) (by linarith) hx
    rw [e1, e2]; simp
  · intro hj'; exact absurd (Finset.mem_range.2 (by omega)) hj'
  · intro hj'; exact absurd (Finset.mem_range.2 (by omega)) hj'

private theorem straddle_tendsto {f : ℝ → ℂ} {K : NNReal} (hf : LipschitzWith K f) {x : ℝ} {f' : ℂ}
    (hd : HasDerivAt f f' x) {u v : ℕ → ℝ} (hu : ∀ N, u N < x) (hv : ∀ N, x < v N)
    (hlim : Filter.Tendsto (fun N => v N - u N) Filter.atTop (nhds 0)) (α β : ℂ) :
    Filter.Tendsto (fun N => β * ((((v N - x) / (v N - u N) : ℝ) : ℂ) * f (u N) +
        (((x - u N) / (v N - u N) : ℝ) : ℂ) * f (v N)) +
      α * ((((1 / (v N - u N)) : ℝ) : ℂ) * (f (v N) - f (u N)))) Filter.atTop (nhds (β * f x + α * f')) := by
  refine (tendsto_const_nhds.mul ?_).add (tendsto_const_nhds.mul ?_)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) (by simpa using hlim.const_mul (K : ℝ))
    have hvu : 0 < v N - u N := by linarith [hu N, hv N]
    have w1 : 0 ≤ (v N - x) / (v N - u N) := div_nonneg (by linarith [hv N]) hvu.le
    have w2 : 0 ≤ (x - u N) / (v N - u N) := div_nonneg (by linarith [hu N]) hvu.le
    have hne := hvu.ne'
    have hsum : (v N - x) / (v N - u N) + (x - u N) / (v N - u N) = 1 := by field_simp; ring
    have hsumC : (((v N - x) / (v N - u N) : ℝ) : ℂ) + (((x - u N) / (v N - u N) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_add, hsum, Complex.ofReal_one]
    have e : (((v N - x) / (v N - u N) : ℝ) : ℂ) * f (u N) + (((x - u N) / (v N - u N) : ℝ) : ℂ) * f (v N) - f x =
        (((v N - x) / (v N - u N) : ℝ) : ℂ) * (f (u N) - f x) +
          (((x - u N) / (v N - u N) : ℝ) : ℂ) * (f (v N) - f x) := by
      linear_combination (f x) * hsumC
    rw [e]
    have n1 : ‖f (u N) - f x‖ ≤ K * (v N - u N) := by
      rw [← dist_eq_norm]
      refine (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ K.2)
      rw [Real.dist_eq, abs_of_neg (by linarith [hu N])]; linarith [hv N]
    have n2 : ‖f (v N) - f x‖ ≤ K * (v N - u N) := by
      rw [← dist_eq_norm]
      refine (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ K.2)
      rw [Real.dist_eq, abs_of_pos (by linarith [hv N])]; linarith [hu N]
    calc _ ≤ ‖(((v N - x) / (v N - u N) : ℝ) : ℂ) * (f (u N) - f x)‖ +
          ‖(((x - u N) / (v N - u N) : ℝ) : ℂ) * (f (v N) - f x)‖ := norm_add_le _ _
      _ = (v N - x) / (v N - u N) * ‖f (u N) - f x‖ + (x - u N) / (v N - u N) * ‖f (v N) - f x‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg w1,
            Real.norm_of_nonneg w2]
      _ ≤ (v N - x) / (v N - u N) * (K * (v N - u N)) + (x - u N) / (v N - u N) * (K * (v N - u N)) :=
          add_le_add (mul_le_mul_of_nonneg_left n1 w1) (mul_le_mul_of_nonneg_left n2 w2)
      _ = K * (v N - u N) := by rw [← add_mul, hsum, one_mul]
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have hlo := hasDerivAt_iff_isLittleO.1 hd
    have hev := hlo.def (half_pos hε)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 hlim) δ hδ
    refine ⟨N0, fun N hN => ?_⟩
    have hd0 := hN0 N hN
    have hvu : 0 < v N - u N := by linarith [hu N, hv N]
    rw [Real.dist_eq, sub_zero, abs_of_pos hvu] at hd0
    have e1 := hball (show dist (v N) x < δ by
      rw [Real.dist_eq, abs_of_pos (by linarith [hv N])]; linarith [hu N])
    have e2 := hball (show dist (u N) x < δ by
      rw [Real.dist_eq, abs_of_neg (by linarith [hu N])]; linarith [hv N])
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hv N])] at e1
    rw [Real.norm_eq_abs, abs_of_neg (by linarith [hu N])] at e2
    rw [dist_eq_norm]
    have hne : (v N : ℂ) - (u N : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]; exact Complex.ofReal_ne_zero.2 hvu.ne'
    have key : (((1 / (v N - u N)) : ℝ) : ℂ) * (f (v N) - f (u N)) - f' =
        (((1 / (v N - u N)) : ℝ) : ℂ) * ((f (v N) - f x - (v N - x) • f') - (f (u N) - f x - (u N - x) • f')) := by
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
      ring
    rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg (one_div_pos.2 hvu).le]
    have hA := norm_sub_le (f (v N) - f x - (v N - x) • f') (f (u N) - f x - (u N - x) • f')
    have hne' := hvu.ne'
    calc _ ≤ 1 / (v N - u N) * (ε / 2 * (v N - x) + ε / 2 * -(u N - x)) :=
          mul_le_mul_of_nonneg_left (hA.trans (add_le_add e1 e2)) (one_div_pos.2 hvu).le
      _ = ε / 2 := by field_simp; ring
      _ < ε := half_lt_self hε

private theorem interp_norm_le {f : ℝ → ℂ} {K : NNReal} (hf : LipschitzWith K f) {a u v x : ℝ} (hfa : f a = 0)
    (hau : a ≤ u) (hux : u < x) (hxv : x < v) (α β : ℂ) :
    ‖β * ((((v - x) / (v - u) : ℝ) : ℂ) * f u + (((x - u) / (v - u) : ℝ) : ℂ) * f v) +
      α * ((((1 / (v - u)) : ℝ) : ℂ) * (f v - f u))‖ ≤ ‖β‖ * (K * (x - a)) + ‖α‖ * K := by
  have hvu : 0 < v - u := by linarith
  have hne := hvu.ne'
  have hfu : ‖f u‖ ≤ K * (u - a) := by
    have := hf.dist_le_mul u a
    rw [dist_eq_norm, hfa, sub_zero, Real.dist_eq, abs_of_nonneg (by linarith)] at this; exact this
  have hfv : ‖f v‖ ≤ K * (v - a) := by
    have := hf.dist_le_mul v a
    rw [dist_eq_norm, hfa, sub_zero, Real.dist_eq, abs_of_nonneg (by linarith)] at this; exact this
  have hfvu : ‖f v - f u‖ ≤ K * (v - u) := by
    have := hf.dist_le_mul v u
    rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (by linarith)] at this; exact this
  have w1 : 0 ≤ (v - x) / (v - u) := div_nonneg (by linarith) hvu.le
  have w2 : 0 ≤ (x - u) / (v - u) := div_nonneg (by linarith) hvu.le
  have hI : ‖(((v - x) / (v - u) : ℝ) : ℂ) * f u + (((x - u) / (v - u) : ℝ) : ℂ) * f v‖ ≤ K * (x - a) := by
    calc _ ≤ ‖(((v - x) / (v - u) : ℝ) : ℂ) * f u‖ + ‖(((x - u) / (v - u) : ℝ) : ℂ) * f v‖ := norm_add_le _ _
      _ = (v - x) / (v - u) * ‖f u‖ + (x - u) / (v - u) * ‖f v‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg w1,
            Real.norm_of_nonneg w2]
      _ ≤ (v - x) / (v - u) * (K * (u - a)) + (x - u) / (v - u) * (K * (v - a)) :=
          add_le_add (mul_le_mul_of_nonneg_left hfu w1) (mul_le_mul_of_nonneg_left hfv w2)
      _ = K * (x - a) := by field_simp; ring
  have hS : ‖(((1 / (v - u)) : ℝ) : ℂ) * (f v - f u)‖ ≤ K := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (one_div_pos.2 hvu).le]
    calc 1 / (v - u) * ‖f v - f u‖ ≤ 1 / (v - u) * (K * (v - u)) :=
          mul_le_mul_of_nonneg_left hfvu (one_div_pos.2 hvu).le
      _ = K := by field_simp
  calc _ ≤ ‖β * ((((v - x) / (v - u) : ℝ) : ℂ) * f u + (((x - u) / (v - u) : ℝ) : ℂ) * f v)‖ +
        ‖α * ((((1 / (v - u)) : ℝ) : ℂ) * (f v - f u))‖ := norm_add_le _ _
    _ ≤ ‖β‖ * (K * (x - a)) + ‖α‖ * K := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hI (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hS (norm_nonneg _))

private theorem tent_int_radial {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a' b' lo hi l m u : ℝ}
    (ha' : 0 ≤ a') (hl : 0 ≤ l) (hlm : l < m) (hmu : m < u) {w : ℝ → ℂ} (hw : Continuous w) :
    IntegrableOn (fun p => w p.2 * SegmentParts.rphi l m u F dF p) (Icc a' b' ×ˢ Icc lo hi) := by
  have hSm : MeasurableSet (Icc a' b' ×ˢ Icc lo hi) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨Mw, hMw⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.continuousOn (s := Icc lo hi))
  have hbox : Icc a' b' ×ˢ Icc lo hi ⊆ Icc 0 b' ×ˢ Icc (-(|lo| + |hi|)) (|lo| + |hi|) :=
    prod_mono (Icc_subset_Icc_left ha') (icc_sub_sym lo hi)
  have hF : IntegrableOn F (Icc a' b' ×ˢ Icc lo hi) := (h.1 b' (|lo| + |hi|)).1.mono_set hbox
  have hrd : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc a' b' ×ˢ Icc lo hi) :=
    (h.1 b' (|lo| + |hi|)).2.mono_set hbox
  have e : (fun p => w p.2 * SegmentParts.rphi l m u F dF p) = fun p =>
      (w p.2 * ((CornerParts.tentSlope l m u p.1 : ℝ) : ℂ)) * F p +
      (w p.2 * (((CornerParts.tentFn l m u p.1 / p.1 : ℝ)) : ℂ)) * ((p.1 : ℂ) * dF p) := by
    funext p
    simp only [SegmentParts.rphi]
    rcases eq_or_ne p.1 0 with h0 | h0
    · rw [h0, tent_at_zero hl hlm hmu]; push_cast; ring
    · have h0' : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
      push_cast; field_simp
  rw [e]
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (w p.2 * ((CornerParts.tentSlope l m u p.1 : ℝ) : ℂ)) * F p)
      (Icc a' b' ×ˢ Icc lo hi) := by
    refine Integrable.bdd_mul (c := |Mw| * (1 / (m - l) + 1 / (u - m))) hF ?_ ?_
    · exact ((hw.comp continuous_snd).measurable.mul
        (Complex.measurable_ofReal.comp ((slope_meas l m u).comp measurable_fst))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hSm] with p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((hMw p.2 hp.2).trans (le_abs_self _)) (slope_abs_le hlm hmu) (abs_nonneg _)
        (abs_nonneg _)
  have h2 : IntegrableOn (fun p : ℝ × ℝ => (w p.2 * (((CornerParts.tentFn l m u p.1 / p.1 : ℝ)) : ℂ)) *
      ((p.1 : ℂ) * dF p)) (Icc a' b' ×ˢ Icc lo hi) := by
    refine Integrable.bdd_mul (c := |Mw| * (1 / (m - l))) hrd ?_ ?_
    · exact ((hw.comp continuous_snd).measurable.mul (Complex.measurable_ofReal.comp
        (((tent_cont l m u).measurable.comp measurable_fst).div measurable_fst))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hSm] with p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul ((hMw p.2 hp.2).trans (le_abs_self _)) ?_ (abs_nonneg _) (abs_nonneg _)
      have hx0 : 0 ≤ p.1 := ha'.trans hp.1.1
      rcases hx0.eq_or_lt with h0 | h0
      · rw [← h0, div_zero, abs_zero]; exact (one_div_pos.2 (sub_pos.2 hlm)).le
      · rw [abs_of_nonneg (div_nonneg (tent_nonneg _ _ _ _) h0.le), div_le_iff₀ h0]
        calc CornerParts.tentFn l m u p.1 ≤ p.1 / (m - l) := tent_le_ramp hl hlm hmu h0.le
          _ = 1 / (m - l) * p.1 := by ring
  exact h1.add h2

private theorem tent_zero_radial {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a b lo hi l m u : ℝ}
    (ha : 0 ≤ a) (hal : a ≤ l) (hlm : l < m) (hmu : m < u) (hub : u ≤ b) {w : ℝ → ℂ} (hw : Continuous w) :
    ∫ p in Icc a b ×ˢ Icc lo hi, w p.2 * SegmentParts.rphi l m u F dF p = 0 := by
  have hl : 0 ≤ l := ha.trans hal
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc)
    (prod_mono (Icc_subset_Icc hal hub) subset_rfl) ?_]
  · rcases hl.lt_or_eq with hl' | hl'
    · exact SegmentParts.radial_pos h hl' hlm hmu w _
    · subst hl'
      have hsplit : (fun p : ℝ × ℝ => w p.2 * SegmentParts.rphi 0 m u F dF p) = fun p =>
          (((w p.2).re : ℝ) : ℂ) * SegmentParts.rphi 0 m u F dF p +
            Complex.I * ((((w p.2).im : ℝ) : ℂ) * SegmentParts.rphi 0 m u F dF p) := by
        funext p
        conv_lhs => rw [← Complex.re_add_im (w p.2)]
        ring
      have i1 : IntegrableOn (fun p : ℝ × ℝ => (((w p.2).re : ℝ) : ℂ) * SegmentParts.rphi 0 m u F dF p)
          (Icc 0 u ×ˢ Icc lo hi) :=
        tent_int_radial h le_rfl le_rfl hlm hmu (w := fun z => (((w z).re : ℝ) : ℂ)) (by fun_prop)
      have i2 : IntegrableOn (fun p : ℝ × ℝ => (((w p.2).im : ℝ) : ℂ) * SegmentParts.rphi 0 m u F dF p)
          (Icc 0 u ×ˢ Icc lo hi) :=
        tent_int_radial h le_rfl le_rfl hlm hmu (w := fun z => (((w z).im : ℝ) : ℂ)) (by fun_prop)
      have r1 : ∫ p in Icc 0 u ×ˢ Icc lo hi, (((w p.2).re : ℝ) : ℂ) * SegmentParts.rphi 0 m u F dF p = 0 :=
        SegmentParts.radial_zero h (t := fun z => (w z).re) (by fun_prop) hlm hmu
      have r2 : ∫ p in Icc 0 u ×ˢ Icc lo hi, (((w p.2).im : ℝ) : ℂ) * SegmentParts.rphi 0 m u F dF p = 0 :=
        SegmentParts.radial_zero h (t := fun z => (w z).im) (by fun_prop) hlm hmu
      rw [hsplit, integral_add i1 (i2.const_mul Complex.I), integral_const_mul, r1, r2]
      simp
  · intro p hp
    have hx : p.1 ∉ Icc l u := fun hx => hp.2 ⟨hx, hp.1.2⟩
    obtain ⟨e1, e2⟩ := tent_outside hlm hmu hx
    simp [SegmentParts.rphi, e1, e2]

private theorem tent_int_height {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {lo hi a b l m u : ℝ}
    (hlm : l < m) (hmu : m < u) {w : ℝ → ℂ} (hw : Continuous w) :
    IntegrableOn (fun p => ((p.1 : ℂ) * w p.1) * SegmentParts.hphi l m u F dF p) (Icc lo hi ×ˢ Icc a b) := by
  have hSm : MeasurableSet (Icc lo hi ×ˢ Icc a b) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨Mw, hMw⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.continuousOn (s := Icc lo hi))
  have hbox : Icc lo hi ×ˢ Icc a b ⊆ Icc (-(|lo| + |hi|)) (|lo| + |hi|) ×ˢ Icc (-(|a| + |b|)) (|a| + |b|) :=
    prod_mono (icc_sub_sym _ _) (icc_sub_sym _ _)
  have hF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc lo hi ×ˢ Icc a b) := (h.1 _ _).1.mono_set hbox
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc lo hi ×ˢ Icc a b) := (h.1 _ _).2.mono_set hbox
  have e : (fun p => ((p.1 : ℂ) * w p.1) * SegmentParts.hphi l m u F dF p) = fun p =>
      (w p.1 * ((CornerParts.tentSlope l m u p.2 : ℝ) : ℂ)) * ((p.1 : ℂ) * F p) +
      (w p.1 * ((CornerParts.tentFn l m u p.2 : ℝ) : ℂ)) * ((p.1 : ℂ) * dF p) := by
    funext p
    simp only [SegmentParts.hphi]
    ring
  rw [e]
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (w p.1 * ((CornerParts.tentSlope l m u p.2 : ℝ) : ℂ)) *
      ((p.1 : ℂ) * F p)) (Icc lo hi ×ˢ Icc a b) := by
    refine Integrable.bdd_mul (c := |Mw| * (1 / (m - l) + 1 / (u - m))) hF ?_ ?_
    · exact ((hw.comp continuous_fst).measurable.mul
        (Complex.measurable_ofReal.comp ((slope_meas l m u).comp measurable_snd))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hSm] with p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((hMw p.1 hp.1).trans (le_abs_self _)) (slope_abs_le hlm hmu) (abs_nonneg _)
        (abs_nonneg _)
  have h2 : IntegrableOn (fun p : ℝ × ℝ => (w p.1 * ((CornerParts.tentFn l m u p.2 : ℝ) : ℂ)) *
      ((p.1 : ℂ) * dF p)) (Icc lo hi ×ˢ Icc a b) := by
    refine Integrable.bdd_mul (c := |Mw| * 1) hdF ?_ ?_
    · exact ((hw.comp continuous_fst).measurable.mul
        (Complex.measurable_ofReal.comp ((tent_cont l m u).measurable.comp measurable_snd))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hSm] with p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _ _ _)]
      exact mul_le_mul ((hMw p.1 hp.1).trans (le_abs_self _)) (tent_le_one hlm hmu) (tent_nonneg _ _ _ _)
        (abs_nonneg _)
  exact h1.add h2

private theorem tent_zero_height {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {lo hi a b l m u : ℝ}
    (hal : a ≤ l) (hlm : l < m) (hmu : m < u) (hub : u ≤ b) (w : ℝ → ℂ) :
    ∫ p in Icc lo hi ×ˢ Icc a b, ((p.1 : ℂ) * w p.1) * SegmentParts.hphi l m u F dF p = 0 := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc)
    (prod_mono subset_rfl (Icc_subset_Icc hal hub)) ?_]
  · exact SegmentParts.height_zero h hlm hmu (fun r => (r : ℂ) * w r) _
  · intro p hp
    have hx : p.2 ∉ Icc l u := fun hx => hp.2 ⟨hp.1.1, hx⟩
    obtain ⟨e1, e2⟩ := tent_outside hlm hmu hx
    simp [SegmentParts.hphi, e1, e2]

private theorem node_term_radial {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a b lo hi : ℝ} (ha : 0 ≤ a)
    {H : ℝ × ℝ → ℂ} (hH : Continuous H) (hHa : ∀ z, H (a, z) = 0) (hHb : ∀ z, H (b, z) = 0)
    {s : ℝ} (hs : 0 < s) {n k : ℕ} (hn : a + (n : ℝ) * s = b) (hk : k ≤ n) :
    IntegrableOn (fun p => H (a + (k : ℝ) * s, p.2) * SegmentParts.rphi (a + ((k : ℝ) - 1) * s) (a + (k : ℝ) * s)
        (a + ((k : ℝ) + 1) * s) F dF p) (Icc a b ×ˢ Icc lo hi) ∧
    ∫ p in Icc a b ×ˢ Icc lo hi, H (a + (k : ℝ) * s, p.2) * SegmentParts.rphi (a + ((k : ℝ) - 1) * s)
        (a + (k : ℝ) * s) (a + ((k : ℝ) + 1) * s) F dF p = 0 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · have hc : ∀ z, H (a + (k : ℝ) * s, z) = 0 := fun z => by
      rw [hk0, Nat.cast_zero, zero_mul, add_zero]; exact hHa z
    simp only [hc, zero_mul]
    exact ⟨integrableOn_zero, by simp⟩
  rcases hk.lt_or_eq with hkn | hkn
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hkn
    have hal : a ≤ a + ((k : ℝ) - 1) * s := by nlinarith
    have hub : a + ((k : ℝ) + 1) * s ≤ b := by rw [← hn]; nlinarith
    have hw : Continuous fun z => H (a + (k : ℝ) * s, z) := by fun_prop
    exact ⟨tent_int_radial h ha (ha.trans hal) (m := a + (k : ℝ) * s) (u := a + ((k : ℝ) + 1) * s)
      (by linarith) (by linarith) hw,
      tent_zero_radial h ha hal (m := a + (k : ℝ) * s) (by linarith) (by linarith) hub hw⟩
  · have hc : ∀ z, H (a + (k : ℝ) * s, z) = 0 := fun z => by rw [hkn, hn]; exact hHb z
    simp only [hc, zero_mul]
    exact ⟨integrableOn_zero, by simp⟩

private theorem node_term_height {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {lo hi a b : ℝ}
    {H : ℝ × ℝ → ℂ} (hH : Continuous H) (hHa : ∀ r, H (r, a) = 0) (hHb : ∀ r, H (r, b) = 0)
    {s : ℝ} (hs : 0 < s) {n k : ℕ} (hn : a + (n : ℝ) * s = b) (hk : k ≤ n) :
    IntegrableOn (fun p => ((p.1 : ℂ) * H (p.1, a + (k : ℝ) * s)) * SegmentParts.hphi (a + ((k : ℝ) - 1) * s)
        (a + (k : ℝ) * s) (a + ((k : ℝ) + 1) * s) F dF p) (Icc lo hi ×ˢ Icc a b) ∧
    ∫ p in Icc lo hi ×ˢ Icc a b, ((p.1 : ℂ) * H (p.1, a + (k : ℝ) * s)) * SegmentParts.hphi
        (a + ((k : ℝ) - 1) * s) (a + (k : ℝ) * s) (a + ((k : ℝ) + 1) * s) F dF p = 0 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · have hc : ∀ r, H (r, a + (k : ℝ) * s) = 0 := fun r => by
      rw [hk0, Nat.cast_zero, zero_mul, add_zero]; exact hHa r
    simp only [hc, mul_zero, zero_mul]
    exact ⟨integrableOn_zero, by simp⟩
  rcases hk.lt_or_eq with hkn | hkn
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hkn
    have hal : a ≤ a + ((k : ℝ) - 1) * s := by nlinarith
    have hub : a + ((k : ℝ) + 1) * s ≤ b := by rw [← hn]; nlinarith
    have hw : Continuous fun r => H (r, a + (k : ℝ) * s) := by fun_prop
    exact ⟨tent_int_height h (l := a + ((k : ℝ) - 1) * s) (m := a + (k : ℝ) * s) (u := a + ((k : ℝ) + 1) * s)
      (by linarith) (by linarith) hw,
      tent_zero_height h hal (m := a + (k : ℝ) * s) (by linarith) (by linarith) hub (fun r => H (r, a + (k : ℝ) * s))⟩
  · have hc : ∀ r, H (r, a + (k : ℝ) * s) = 0 := fun r => by rw [hkn, hn]; exact hHb r
    simp only [hc, mul_zero, zero_mul]
    exact ⟨integrableOn_zero, by simp⟩

private theorem step_facts {a b : ℝ} (hab : a < b) :
    (∀ N : ℕ, 0 < (b - a) / ((N : ℝ) + 1)) ∧ (∀ N : ℕ, a + ((N + 1 : ℕ) : ℝ) * ((b - a) / ((N : ℝ) + 1)) = b) ∧
    Filter.Tendsto (fun N : ℕ => (b - a) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
  refine ⟨fun N => div_pos (sub_pos.2 hab) (by positivity), fun N => ?_, ?_⟩
  · have : (N : ℝ) + 1 ≠ 0 := by positivity
    push_cast; field_simp; ring
  · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)
    simpa only [mul_zero, mul_one_div] using this

private theorem off_grid {a b x : ℝ} (N : ℕ)
    (hG : x ∉ range (fun q : ℚ => a + (q : ℝ) * (b - a))) :
    ∀ k : ℕ, x ≠ a + (k : ℝ) * ((b - a) / ((N : ℝ) + 1)) := by
  intro k e
  apply hG
  refine ⟨(k : ℚ) / ((N : ℚ) + 1), ?_⟩
  simp only
  rw [e]; push_cast; ring

private theorem slope_slice_fst {H : ℝ × ℝ → ℂ} {C : NNReal} (hH : LipschitzWith C H) (z : ℝ) :
    LipschitzWith C (fun r => H (r, z)) := by
  have := hH.comp (LipschitzWith.prodMk_right z); rwa [mul_one] at this

private theorem slope_slice_snd {H : ℝ × ℝ → ℂ} {C : NNReal} (hH : LipschitzWith C H) (r : ℝ) :
    LipschitzWith C (fun z => H (r, z)) := by
  have := hH.comp (LipschitzWith.prodMk_left r); rwa [mul_one] at this

private theorem radial_core {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a b lo hi : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {H : ℝ × ℝ → ℂ} {C : NNReal} (hH : LipschitzWith C H)
    (hHa : ∀ z, H (a, z) = 0) (hHb : ∀ z, H (b, z) = 0) :
    IntegrableOn (fun p => dF p * H p + F p * CellBox.radialDeriv H p) (Icc a b ×ˢ Icc lo hi) ∧
    ∫ p in Icc a b ×ˢ Icc lo hi, (dF p * H p + F p * CellBox.radialDeriv H p) = 0 := by
  have hSm : MeasurableSet (Icc a b ×ˢ Icc lo hi) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨hspos, hsend, hs0⟩ := step_facts hab
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℝ, s = fun N : ℕ => (b - a) / ((N : ℝ) + 1) := ⟨_, rfl⟩
  have hspos' : ∀ N, 0 < s N := fun N => by rw [hsdef]; exact hspos N
  have hsend' : ∀ N, a + ((N + 1 : ℕ) : ℝ) * s N = b := fun N => by rw [hsdef]; exact hsend N
  have hs0' : Filter.Tendsto s Filter.atTop (nhds 0) := by rw [hsdef]; exact hs0
  have hoff : ∀ N, ∀ x, x ∉ range (fun q : ℚ => a + (q : ℝ) * (b - a)) → ∀ k : ℕ, x ≠ a + (k : ℝ) * s N :=
    fun N x hG => by rw [hsdef]; exact off_grid N hG
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ × ℝ → ℂ, A = fun N p => ∑ k ∈ Finset.range (N + 1 + 1),
      H (a + (k : ℝ) * s N, p.2) * SegmentParts.rphi (a + ((k : ℝ) - 1) * s N) (a + (k : ℝ) * s N)
        (a + ((k : ℝ) + 1) * s N) F dF p := ⟨_, rfl⟩
  have hAint : ∀ N, IntegrableOn (A N) (Icc a b ×ˢ Icc lo hi) := fun N => by
    simp only [hAdef]
    exact integrable_finsetSum _ fun k hk => (node_term_radial h ha hH.continuous hHa hHb (lo := lo) (hi := hi)
      (hspos' N) (hsend' N) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).1
  have hA0 : ∀ N, ∫ p in Icc a b ×ˢ Icc lo hi, A N p = 0 := fun N => by
    simp only [hAdef]
    rw [integral_finsetSum _ fun k hk => (node_term_radial h ha hH.continuous hHa hHb (lo := lo) (hi := hi)
      (hspos' N) (hsend' N) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).1]
    exact Finset.sum_eq_zero fun k hk => (node_term_radial h ha hH.continuous hHa hHb (lo := lo) (hi := hi)
      (hspos' N) (hsend' N) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).2
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℝ, T = insert a (insert b (range fun q : ℚ => a + (q : ℝ) * (b - a))) :=
    ⟨_, rfl⟩
  have hTc : T.Countable := by rw [hTdef]; exact ((countable_range _).insert b).insert a
  have hT0 : ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)), p.1 ∉ T := by
    refine ae_restrict_of_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (null_fst_set hTc)] with p hp
    exact fun h' => hp ⟨h', mem_univ _⟩
  have hform : ∀ p ∈ Icc a b ×ˢ Icc lo hi, p.1 ∉ T → ∀ N, ∃ u v : ℝ, u < p.1 ∧ p.1 < v ∧ a ≤ u ∧
      v - u = s N ∧ A N p = dF p * ((((v - p.1) / (v - u) : ℝ) : ℂ) * H (u, p.2) +
        (((p.1 - u) / (v - u) : ℝ) : ℂ) * H (v, p.2)) +
        F p * ((((1 / (v - u)) : ℝ) : ℂ) * (H (v, p.2) - H (u, p.2))) := by
    intro p hp hpT N
    have ha' : p.1 ≠ a := fun e => hpT (by rw [hTdef]; exact mem_insert_iff.2 (Or.inl e))
    have hb' : p.1 ≠ b := fun e => hpT (by rw [hTdef]; exact mem_insert_of_mem _ (mem_insert_iff.2 (Or.inl e)))
    have hG : p.1 ∉ range (fun q : ℚ => a + (q : ℝ) * (b - a)) := fun e =>
      hpT (by rw [hTdef]; exact mem_insert_of_mem _ (mem_insert_of_mem _ e))
    have hx1 : a < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm ha')
    have hx2 : p.1 < b := lt_of_le_of_ne hp.1.2 hb'
    obtain ⟨j, hj, h1, h2⟩ := grid_cell (hspos' N) (n := N + 1) hx1 (by rw [hsend' N]; exact hx2)
      (hoff N _ hG)
    refine ⟨a + (j : ℝ) * s N, a + ((j : ℝ) + 1) * s N, h1, h2, ?_, by ring, ?_⟩
    · have : (0 : ℝ) ≤ (j : ℝ) * s N := mul_nonneg (Nat.cast_nonneg j) (hspos' N).le
      linarith
    · have e := grid_sum (fun r => H (r, p.2)) (F p) (dF p) (hspos' N) hj h1 h2
      beta_reduce at e
      have hw : a + ((j : ℝ) + 1) * s N - (a + (j : ℝ) * s N) = s N := by ring
      rw [hw]
      simp only [hAdef, SegmentParts.rphi]
      linear_combination e
  have hmem : ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)), p ∈ Icc a b ×ˢ Icc lo hi := ae_restrict_mem hSm
  have hdiff : ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)), DifferentiableAt ℝ (fun r => H (r, p.2)) p.1 :=
    ae_restrict_of_ae (ae_diff_fst hH)
  have hlim : ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)),
      Filter.Tendsto (fun N => A N p) Filter.atTop (nhds (dF p * H p + F p * CellBox.radialDeriv H p)) := by
    filter_upwards [hmem, hT0, hdiff] with p hp hpT hpd
    choose u v hu hv _ hvu hAe using hform p hp hpT
    have hL := straddle_tendsto (f := fun r => H (r, p.2)) (slope_slice_fst hH p.2)
      hpd.hasDerivAt hu hv (by simp only [hvu]; exact hs0') (F p) (dF p)
    exact hL.congr fun N => (hAe N).symm
  have hbound : ∀ N, ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)),
      ‖A N p‖ ≤ (C : ℝ) * ‖(p.1 : ℂ) * dF p‖ + (C : ℝ) * ‖F p‖ := by
    intro N
    filter_upwards [hmem, hT0] with p hp hpT
    obtain ⟨u, v, hu, hv, hau, -, hAe⟩ := hform p hp hpT N
    rw [hAe]
    refine (interp_norm_le (f := fun r => H (r, p.2)) (slope_slice_fst hH p.2) (hHa p.2)
      hau hu hv (F p) (dF p)).trans ?_
    have hx0 : 0 ≤ p.1 := ha.trans hp.1.1
    rw [norm_mul (p.1 : ℂ), Complex.norm_real, Real.norm_of_nonneg hx0]
    have := mul_nonneg (mul_nonneg (NNReal.coe_nonneg C) (norm_nonneg (dF p))) ha
    nlinarith [this]
  have hF : IntegrableOn F (Icc a b ×ˢ Icc lo hi) :=
    (h.1 b (|lo| + |hi|)).1.mono_set (prod_mono (Icc_subset_Icc_left ha) (icc_sub_sym lo hi))
  have hrd : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc a b ×ˢ Icc lo hi) :=
    (h.1 b (|lo| + |hi|)).2.mono_set (prod_mono (Icc_subset_Icc_left ha) (icc_sub_sym lo hi))
  have hgint : Integrable (fun p : ℝ × ℝ => (C : ℝ) * ‖(p.1 : ℂ) * dF p‖ + (C : ℝ) * ‖F p‖)
      (volume.restrict (Icc a b ×ˢ Icc lo hi)) := (hrd.norm.const_mul _).add (hF.norm.const_mul _)
  have hAm : ∀ N, AEStronglyMeasurable (A N) (volume.restrict (Icc a b ×ˢ Icc lo hi)) :=
    fun N => (hAint N).aestronglyMeasurable
  have hfm := aestronglyMeasurable_of_tendsto_ae Filter.atTop hAm hlim
  have hfb : ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)),
      ‖dF p * H p + F p * CellBox.radialDeriv H p‖ ≤ (C : ℝ) * ‖(p.1 : ℂ) * dF p‖ + (C : ℝ) * ‖F p‖ := by
    filter_upwards [hlim, ae_all_iff.2 hbound] with p hp hb
    exact le_of_tendsto' hp.norm hb
  refine ⟨Integrable.mono' hgint hfm hfb, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence _ hAm hgint hbound hlim
  simp only [hA0] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

private theorem height_core {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {lo hi a b : ℝ}
    (hab : a < b) {H : ℝ × ℝ → ℂ} {C : NNReal} (hH : LipschitzWith C H)
    (hHa : ∀ r, H (r, a) = 0) (hHb : ∀ r, H (r, b) = 0) :
    IntegrableOn (fun p => (p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p)) (Icc lo hi ×ˢ Icc a b) ∧
    ∫ p in Icc lo hi ×ˢ Icc a b, (p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p) = 0 := by
  have hSm : MeasurableSet (Icc lo hi ×ˢ Icc a b) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨hspos, hsend, hs0⟩ := step_facts hab
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℝ, s = fun N : ℕ => (b - a) / ((N : ℝ) + 1) := ⟨_, rfl⟩
  have hspos' : ∀ N, 0 < s N := fun N => by rw [hsdef]; exact hspos N
  have hsend' : ∀ N, a + ((N + 1 : ℕ) : ℝ) * s N = b := fun N => by rw [hsdef]; exact hsend N
  have hs0' : Filter.Tendsto s Filter.atTop (nhds 0) := by rw [hsdef]; exact hs0
  have hoff : ∀ N, ∀ x, x ∉ range (fun q : ℚ => a + (q : ℝ) * (b - a)) → ∀ k : ℕ, x ≠ a + (k : ℝ) * s N :=
    fun N x hG => by rw [hsdef]; exact off_grid N hG
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ × ℝ → ℂ, A = fun N p => ∑ k ∈ Finset.range (N + 1 + 1),
      ((p.1 : ℂ) * H (p.1, a + (k : ℝ) * s N)) * SegmentParts.hphi (a + ((k : ℝ) - 1) * s N) (a + (k : ℝ) * s N)
        (a + ((k : ℝ) + 1) * s N) F dF p := ⟨_, rfl⟩
  have hAint : ∀ N, IntegrableOn (A N) (Icc lo hi ×ˢ Icc a b) := fun N => by
    simp only [hAdef]
    exact integrable_finsetSum _ fun k hk => (node_term_height h hH.continuous hHa hHb (lo := lo) (hi := hi)
      (hspos' N) (hsend' N) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).1
  have hA0 : ∀ N, ∫ p in Icc lo hi ×ˢ Icc a b, A N p = 0 := fun N => by
    simp only [hAdef]
    rw [integral_finsetSum _ fun k hk => (node_term_height h hH.continuous hHa hHb (lo := lo) (hi := hi)
      (hspos' N) (hsend' N) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).1]
    exact Finset.sum_eq_zero fun k hk => (node_term_height h hH.continuous hHa hHb (lo := lo) (hi := hi)
      (hspos' N) (hsend' N) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).2
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℝ, T = insert a (insert b (range fun q : ℚ => a + (q : ℝ) * (b - a))) :=
    ⟨_, rfl⟩
  have hTc : T.Countable := by rw [hTdef]; exact ((countable_range _).insert b).insert a
  have hT0 : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)), p.2 ∉ T := by
    refine ae_restrict_of_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (null_snd_set hTc)] with p hp
    exact fun h' => hp ⟨mem_univ _, h'⟩
  have hform : ∀ p ∈ Icc lo hi ×ˢ Icc a b, p.2 ∉ T → ∀ N, ∃ u v : ℝ, u < p.2 ∧ p.2 < v ∧ a ≤ u ∧
      v - u = s N ∧ A N p = (p.1 : ℂ) * (dF p * ((((v - p.2) / (v - u) : ℝ) : ℂ) * H (p.1, u) +
        (((p.2 - u) / (v - u) : ℝ) : ℂ) * H (p.1, v)) +
        F p * ((((1 / (v - u)) : ℝ) : ℂ) * (H (p.1, v) - H (p.1, u)))) := by
    intro p hp hpT N
    have ha' : p.2 ≠ a := fun e => hpT (by rw [hTdef]; exact mem_insert_iff.2 (Or.inl e))
    have hb' : p.2 ≠ b := fun e => hpT (by rw [hTdef]; exact mem_insert_of_mem _ (mem_insert_iff.2 (Or.inl e)))
    have hG : p.2 ∉ range (fun q : ℚ => a + (q : ℝ) * (b - a)) := fun e =>
      hpT (by rw [hTdef]; exact mem_insert_of_mem _ (mem_insert_of_mem _ e))
    have hx1 : a < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm ha')
    have hx2 : p.2 < b := lt_of_le_of_ne hp.2.2 hb'
    obtain ⟨j, hj, h1, h2⟩ := grid_cell (hspos' N) (n := N + 1) hx1 (by rw [hsend' N]; exact hx2)
      (hoff N _ hG)
    refine ⟨a + (j : ℝ) * s N, a + ((j : ℝ) + 1) * s N, h1, h2, ?_, by ring, ?_⟩
    · have : (0 : ℝ) ≤ (j : ℝ) * s N := mul_nonneg (Nat.cast_nonneg j) (hspos' N).le
      linarith
    · have e := grid_sum (fun z => H (p.1, z)) (F p) (dF p) (hspos' N) hj h1 h2
      beta_reduce at e
      have hw : a + ((j : ℝ) + 1) * s N - (a + (j : ℝ) * s N) = s N := by ring
      rw [hw]
      simp only [hAdef, SegmentParts.hphi]
      have e2 : ∑ k ∈ Finset.range (N + 1 + 1), ((p.1 : ℂ) * H (p.1, a + (k : ℝ) * s N)) *
          (((CornerParts.tentSlope (a + ((k : ℝ) - 1) * s N) (a + (k : ℝ) * s N) (a + ((k : ℝ) + 1) * s N) p.2 : ℝ) : ℂ) * F p +
            ((CornerParts.tentFn (a + ((k : ℝ) - 1) * s N) (a + (k : ℝ) * s N) (a + ((k : ℝ) + 1) * s N) p.2 : ℝ) : ℂ) * dF p) =
          (p.1 : ℂ) * ∑ k ∈ Finset.range (N + 1 + 1), H (p.1, a + (k : ℝ) * s N) *
          (((CornerParts.tentSlope (a + ((k : ℝ) - 1) * s N) (a + (k : ℝ) * s N) (a + ((k : ℝ) + 1) * s N) p.2 : ℝ) : ℂ) * F p +
            ((CornerParts.tentFn (a + ((k : ℝ) - 1) * s N) (a + (k : ℝ) * s N) (a + ((k : ℝ) + 1) * s N) p.2 : ℝ) : ℂ) * dF p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e2, e]
  have hmem : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)), p ∈ Icc lo hi ×ˢ Icc a b := ae_restrict_mem hSm
  have hdiff : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)), DifferentiableAt ℝ (fun z => H (p.1, z)) p.2 :=
    ae_restrict_of_ae (ae_diff_snd hH)
  have hlim : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)),
      Filter.Tendsto (fun N => A N p) Filter.atTop
        (nhds ((p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p))) := by
    filter_upwards [hmem, hT0, hdiff] with p hp hpT hpd
    choose u v hu hv _ hvu hAe using hform p hp hpT
    have hL := straddle_tendsto (f := fun z => H (p.1, z)) (slope_slice_snd hH p.1)
      hpd.hasDerivAt hu hv (by simp only [hvu]; exact hs0') (F p) (dF p)
    exact (tendsto_const_nhds.mul hL).congr fun N => (hAe N).symm
  have hbound : ∀ N, ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)),
      ‖A N p‖ ≤ (C : ℝ) * (b - a) * ‖(p.1 : ℂ) * dF p‖ + (C : ℝ) * ‖(p.1 : ℂ) * F p‖ := by
    intro N
    filter_upwards [hmem, hT0] with p hp hpT
    obtain ⟨u, v, hu, hv, hau, -, hAe⟩ := hform p hp hpT N
    have hI := interp_norm_le (f := fun z => H (p.1, z)) (slope_slice_snd hH p.1) (hHa p.1) hau hu hv (F p) (dF p)
    rw [hAe, norm_mul, norm_mul (p.1 : ℂ) (dF p), norm_mul (p.1 : ℂ) (F p)]
    refine (mul_le_mul_of_nonneg_left hI (norm_nonneg _)).trans ?_
    have hz : p.2 - a ≤ b - a := by linarith [hp.2.2]
    have k1 : ‖(p.1 : ℂ)‖ * ‖dF p‖ * (C : ℝ) * (p.2 - a) ≤ ‖(p.1 : ℂ)‖ * ‖dF p‖ * (C : ℝ) * (b - a) :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (NNReal.coe_nonneg C))
    nlinarith [k1]
  have hbox : Icc lo hi ×ˢ Icc a b ⊆ Icc (-(|lo| + |hi|)) (|lo| + |hi|) ×ˢ Icc (-(|a| + |b|)) (|a| + |b|) :=
    prod_mono (icc_sub_sym _ _) (icc_sub_sym _ _)
  have hF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc lo hi ×ˢ Icc a b) := (h.1 _ _).1.mono_set hbox
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc lo hi ×ˢ Icc a b) := (h.1 _ _).2.mono_set hbox
  have hgint : Integrable (fun p : ℝ × ℝ => (C : ℝ) * (b - a) * ‖(p.1 : ℂ) * dF p‖ + (C : ℝ) * ‖(p.1 : ℂ) * F p‖)
      (volume.restrict (Icc lo hi ×ˢ Icc a b)) := (hdF.norm.const_mul _).add (hF.norm.const_mul _)
  have hAm : ∀ N, AEStronglyMeasurable (A N) (volume.restrict (Icc lo hi ×ˢ Icc a b)) :=
    fun N => (hAint N).aestronglyMeasurable
  have hfm := aestronglyMeasurable_of_tendsto_ae Filter.atTop hAm hlim
  have hfb : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)),
      ‖(p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p)‖ ≤
        (C : ℝ) * (b - a) * ‖(p.1 : ℂ) * dF p‖ + (C : ℝ) * ‖(p.1 : ℂ) * F p‖ := by
    filter_upwards [hlim, ae_all_iff.2 hbound] with p hp hb
    exact le_of_tendsto' hp.norm hb
  refine ⟨Integrable.mono' hgint hfm hfb, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence _ hAm hgint hbound hlim
  simp only [hA0] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem radial_slope_zero {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a b lo hi : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {H : ℝ × ℝ → ℂ} {C : NNReal} (hH : LipschitzOnWith C H (Icc a b ×ˢ Icc lo hi))
    (hHa : ∀ z ∈ Icc lo hi, H (a, z) = 0) (hHb : ∀ z ∈ Icc lo hi, H (b, z) = 0) :
    IntegrableOn (fun p => dF p * H p + F p * CellBox.radialDeriv H p) (Icc a b ×ˢ Icc lo hi) ∧
    ∫ p in Icc a b ×ˢ Icc lo hi, (dF p * H p + F p * CellBox.radialDeriv H p) = 0 := by
  rcases lt_or_ge hi lo with hlh | hlh
  · have he : Icc a b ×ˢ Icc lo hi = (∅ : Set (ℝ × ℝ)) := by rw [Icc_eq_empty_of_lt hlh, prod_empty]
    simp [he]
  have hSm : MeasurableSet (Icc a b ×ˢ Icc lo hi) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ,
      G = fun p => H ((projIcc a b hab.le p.1 : ℝ), (projIcc lo hi hlh p.2 : ℝ)) := ⟨_, rfl⟩
  have hG : LipschitzWith C G := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [hGdef]
    refine (hH.dist_le_mul _ ⟨(projIcc a b hab.le p.1).2, (projIcc lo hi hlh p.2).2⟩ _
      ⟨(projIcc a b hab.le q.1).2, (projIcc lo hi hlh q.2).2⟩).trans (mul_le_mul_of_nonneg_left ?_ C.2)
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hab.le).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hlh).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  have hGa : ∀ z, G (a, z) = 0 := fun z => by
    rw [hGdef]; simp only [projIcc_left]; exact hHa _ (projIcc lo hi hlh z).2
  have hGb : ∀ z, G (b, z) = 0 := fun z => by
    rw [hGdef]; simp only [projIcc_right]; exact hHb _ (projIcc lo hi hlh z).2
  have heq : ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)),
      dF p * G p + F p * CellBox.radialDeriv G p = dF p * H p + F p * CellBox.radialDeriv H p := by
    have h1 := compl_mem_ae_iff.mpr (null_fst_set (countable_singleton a))
    have h2 := compl_mem_ae_iff.mpr (null_fst_set (countable_singleton b))
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae h1, ae_restrict_of_ae h2] with p hmem hp1 hp2
    have hpa : p.1 ≠ a := fun e => hp1 ⟨e, mem_univ _⟩
    have hpb : p.1 ≠ b := fun e => hp2 ⟨e, mem_univ _⟩
    have hio : p.1 ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.1.1 (Ne.symm hpa), lt_of_le_of_ne hmem.1.2 hpb⟩
    have hloc : (fun r => G (r, p.2)) =ᶠ[nhds p.1] (fun r => H (r, p.2)) := by
      filter_upwards [Icc_mem_nhds hio.1 hio.2] with r hr
      rw [hGdef]; simp only [projIcc_of_mem hab.le hr, projIcc_of_mem hlh hmem.2]
    have hd : CellBox.radialDeriv G p = CellBox.radialDeriv H p := hloc.deriv_eq
    rw [hd, show G p = H p from hloc.eq_of_nhds]
  obtain ⟨hI, hE⟩ := radial_core h ha hab hG hGa hGb (lo := lo) (hi := hi)
  refine ⟨hI.congr heq, ?_⟩
  rw [← integral_congr_ae heq]; exact hE

theorem height_slope_zero {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {lo hi a b : ℝ}
    (hlo : 0 ≤ lo) (hab : a < b) {H : ℝ × ℝ → ℂ} {C : NNReal} (hH : LipschitzOnWith C H (Icc lo hi ×ˢ Icc a b))
    (hHa : ∀ r ∈ Icc lo hi, H (r, a) = 0) (hHb : ∀ r ∈ Icc lo hi, H (r, b) = 0) :
    IntegrableOn (fun p => (p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p)) (Icc lo hi ×ˢ Icc a b) ∧
    ∫ p in Icc lo hi ×ˢ Icc a b, (p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p) = 0 := by
  rcases lt_or_ge hi lo with hlh | hlh
  · have he : Icc lo hi ×ˢ Icc a b = (∅ : Set (ℝ × ℝ)) := by rw [Icc_eq_empty_of_lt hlh, empty_prod]
    simp [he]
  have hSm : MeasurableSet (Icc lo hi ×ˢ Icc a b) := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ,
      G = fun p => H ((projIcc lo hi hlh p.1 : ℝ), (projIcc a b hab.le p.2 : ℝ)) := ⟨_, rfl⟩
  have hG : LipschitzWith C G := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [hGdef]
    refine (hH.dist_le_mul _ ⟨(projIcc lo hi hlh p.1).2, (projIcc a b hab.le p.2).2⟩ _
      ⟨(projIcc lo hi hlh q.1).2, (projIcc a b hab.le q.2).2⟩).trans (mul_le_mul_of_nonneg_left ?_ C.2)
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hlh).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hab.le).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  have hGa : ∀ r, G (r, a) = 0 := fun r => by
    rw [hGdef]; simp only [projIcc_left]; exact hHa _ (projIcc lo hi hlh r).2
  have hGb : ∀ r, G (r, b) = 0 := fun r => by
    rw [hGdef]; simp only [projIcc_right]; exact hHb _ (projIcc lo hi hlh r).2
  have heq : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)),
      (p.1 : ℂ) * (dF p * G p + F p * CellBox.heightDeriv G p) =
        (p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p) := by
    have h1 := compl_mem_ae_iff.mpr (null_snd_set (countable_singleton a))
    have h2 := compl_mem_ae_iff.mpr (null_snd_set (countable_singleton b))
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae h1, ae_restrict_of_ae h2] with p hmem hp1 hp2
    have hpa : p.2 ≠ a := fun e => hp1 ⟨mem_univ _, e⟩
    have hpb : p.2 ≠ b := fun e => hp2 ⟨mem_univ _, e⟩
    have hio : p.2 ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.2.1 (Ne.symm hpa), lt_of_le_of_ne hmem.2.2 hpb⟩
    have hloc : (fun z => G (p.1, z)) =ᶠ[nhds p.2] (fun z => H (p.1, z)) := by
      filter_upwards [Icc_mem_nhds hio.1 hio.2] with z hz
      rw [hGdef]; simp only [projIcc_of_mem hlh hmem.1, projIcc_of_mem hab.le hz]
    have hd : CellBox.heightDeriv G p = CellBox.heightDeriv H p := hloc.deriv_eq
    rw [hd, show G p = H p from hloc.eq_of_nhds]
  obtain ⟨hI, hE⟩ := height_core h hab hG hGa hGb (lo := lo) (hi := hi)
  refine ⟨hI.congr heq, ?_⟩
  rw [← integral_congr_ae heq]; exact hE

private theorem slope_bound_le {f : ℝ × ℝ → ℂ} {C : NNReal} {T : Set (ℝ × ℝ)} (hf : LipschitzOnWith C f T)
    (hT : IsCompact T) : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ T, ‖f p‖ ≤ M := by
  obtain ⟨M, hM⟩ := hT.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨|M|, abs_nonneg M, fun p hp => (hM p hp).trans (le_abs_self M)⟩

private theorem slope_mul_bound {f g : ℝ × ℝ → ℂ} {Cf Cg : NNReal} {T : Set (ℝ × ℝ)} (hf : LipschitzOnWith Cf f T)
    (hg : LipschitzOnWith Cg g T) {Mf Mg : ℝ} (hMf : ∀ p ∈ T, ‖f p‖ ≤ Mf) (hMg : ∀ p ∈ T, ‖g p‖ ≤ Mg)
    (hMf0 : 0 ≤ Mf) (hMg0 : 0 ≤ Mg) :
    LipschitzOnWith (Real.toNNReal (Mf * Cg + Mg * Cf)) (fun p => f p * g p) T := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have e : f p * g p - f q * g q = f p * (g p - g q) + (f p - f q) * g q := by ring
  rw [e]
  have h1 : ‖g p - g q‖ ≤ Cg * dist p q := by rw [← dist_eq_norm]; exact hg.dist_le_mul p hp q hq
  have h2 : ‖f p - f q‖ ≤ Cf * dist p q := by rw [← dist_eq_norm]; exact hf.dist_le_mul p hp q hq
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hd : 0 ≤ dist p q := dist_nonneg
  calc ‖f p‖ * ‖g p - g q‖ + ‖f p - f q‖ * ‖g q‖ ≤ Mf * (Cg * dist p q) + (Cf * dist p q) * Mg :=
        add_le_add (mul_le_mul (hMf p hp) h1 (norm_nonneg _) hMf0)
          (mul_le_mul h2 (hMg q hq) (norm_nonneg _) (by positivity))
    _ = (Mf * Cg + Mg * Cf) * dist p q := by ring

private theorem ramp_slope_bound (o e : ℝ) (T : Set (ℝ × ℝ)) :
    LipschitzOnWith (Real.toNNReal |1 / e|) (fun p : ℝ × ℝ => (((p.1 - o) / e : ℝ) : ℂ)) T := by
  refine LipschitzOnWith.of_dist_le_mul fun p _ q _ => ?_
  rw [Real.coe_toNNReal _ (abs_nonneg _), dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have e1 : (p.1 - o) / e - (q.1 - o) / e = (1 / e) * (p.1 - q.1) := by ring
  rw [e1, abs_mul]
  have h2 : |p.1 - q.1| ≤ dist p q := by rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

private theorem ramp2_slope_bound (o e : ℝ) (T : Set (ℝ × ℝ)) :
    LipschitzOnWith (Real.toNNReal |1 / e|) (fun p : ℝ × ℝ => (((p.2 - o) / e : ℝ) : ℂ)) T := by
  refine LipschitzOnWith.of_dist_le_mul fun p _ q _ => ?_
  rw [Real.coe_toNNReal _ (abs_nonneg _), dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have e1 : (p.2 - o) / e - (q.2 - o) / e = (1 / e) * (p.2 - q.2) := by ring
  rw [e1, abs_mul]
  have h2 : |p.2 - q.2| ≤ dist p q := by rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_right _ _
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

private theorem null_line (v : ℝ) : (volume : Measure (ℝ × ℝ)) ({v} ×ˢ univ) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]; simp

private theorem null_line2 (v : ℝ) : (volume : Measure (ℝ × ℝ)) (univ ×ˢ {v}) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]; simp

private theorem ae_line_diff {G : ℝ × ℝ → ℂ} {C : NNReal} {a b lo hi : ℝ} (hab : a ≤ b) (hlh : lo ≤ hi)
    (hG : LipschitzOnWith C G (Icc a b ×ˢ Icc lo hi)) :
    ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)), DifferentiableAt ℝ (fun r => G (r, p.2)) p.1 := by
  let P : ℝ × ℝ → ℝ × ℝ := fun p => ((projIcc a b hab p.1 : ℝ), (projIcc lo hi hlh p.2 : ℝ))
  have hPmem : ∀ p, P p ∈ Icc a b ×ˢ Icc lo hi := fun p => ⟨(projIcc a b hab p.1).2, (projIcc lo hi hlh p.2).2⟩
  have hPid : ∀ p ∈ Icc a b ×ˢ Icc lo hi, P p = p := fun p hp =>
    Prod.ext (by simp [P, projIcc_of_mem hab hp.1]) (by simp [P, projIcc_of_mem hlh hp.2])
  have hPd : ∀ p q, dist (P p) (P q) ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hab).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hlh).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  set g : ℝ × ℝ → ℂ := fun p => G (P p) with hgdef
  have hg : LipschitzWith C g := LipschitzWith.of_dist_le_mul fun p q =>
    (hG.dist_le_mul _ (hPmem p) _ (hPmem q)).trans (mul_le_mul_of_nonneg_left (hPd p q) C.2)
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun r => g (r, x.2)) x.1} := by
    have h0 := measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun z r => g (r, z))
      (hg.continuous.comp continuous_swap)
    exact measurable_swap h0
  have hall : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun r => g (r, x.2)) x.1 := by
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas, Measure.ae_ae_comm hmeas]
    refine Filter.Eventually.of_forall fun z => ?_
    have hl : LipschitzWith (C * 1) (fun r => g (r, z)) := hg.comp (LipschitzWith.prodMk_right z)
    exact hl.ae_differentiableAt_real
  have h1 := compl_mem_ae_iff.mpr (null_line a)
  have h2 := compl_mem_ae_iff.mpr (null_line b)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with p hp hmem hp1 hp2
  have hpa : p.1 ≠ a := fun e => hp1 ⟨e, mem_univ _⟩
  have hpb : p.1 ≠ b := fun e => hp2 ⟨e, mem_univ _⟩
  have hio : p.1 ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.1.1 (Ne.symm hpa), lt_of_le_of_ne hmem.1.2 hpb⟩
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hio.1 hio.2] with r hr
  simp only [hgdef, hPid (r, p.2) ⟨hr, hmem.2⟩]

private theorem ae_line_diff2 {G : ℝ × ℝ → ℂ} {C : NNReal} {lo hi a b : ℝ} (hlh : lo ≤ hi) (hab : a ≤ b)
    (hG : LipschitzOnWith C G (Icc lo hi ×ˢ Icc a b)) :
    ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)), DifferentiableAt ℝ (fun z => G (p.1, z)) p.2 := by
  let P : ℝ × ℝ → ℝ × ℝ := fun p => ((projIcc lo hi hlh p.1 : ℝ), (projIcc a b hab p.2 : ℝ))
  have hPmem : ∀ p, P p ∈ Icc lo hi ×ˢ Icc a b := fun p => ⟨(projIcc lo hi hlh p.1).2, (projIcc a b hab p.2).2⟩
  have hPid : ∀ p ∈ Icc lo hi ×ˢ Icc a b, P p = p := fun p hp =>
    Prod.ext (by simp [P, projIcc_of_mem hlh hp.1]) (by simp [P, projIcc_of_mem hab hp.2])
  have hPd : ∀ p q, dist (P p) (P q) ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hlh).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hab).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  set g : ℝ × ℝ → ℂ := fun p => G (P p) with hgdef
  have hg : LipschitzWith C g := LipschitzWith.of_dist_le_mul fun p q =>
    (hG.dist_le_mul _ (hPmem p) _ (hPmem q)).trans (mul_le_mul_of_nonneg_left (hPd p q) C.2)
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun z => g (x.1, z)) x.2} :=
    measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun r z => g (r, z)) hg.continuous
  have hall : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun z => g (x.1, z)) x.2 := by
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
    refine Filter.Eventually.of_forall fun r => ?_
    have hl : LipschitzWith (C * 1) (fun z => g (r, z)) := hg.comp (LipschitzWith.prodMk_left r)
    exact hl.ae_differentiableAt_real
  have h1 := compl_mem_ae_iff.mpr (null_line2 a)
  have h2 := compl_mem_ae_iff.mpr (null_line2 b)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with p hp hmem hp1 hp2
  have hpa : p.2 ≠ a := fun e => hp1 ⟨mem_univ _, e⟩
  have hpb : p.2 ≠ b := fun e => hp2 ⟨mem_univ _, e⟩
  have hio : p.2 ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.2.1 (Ne.symm hpa), lt_of_le_of_ne hmem.2.2 hpb⟩
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hio.1 hio.2] with z hz
  simp only [hgdef, hPid (p.1, z) ⟨hmem.1, hz⟩]

private theorem box_sub' (a b : ℝ) : Icc a b ⊆ Icc (-(|a| + |b|)) (|a| + |b|) := by
  intro s hs
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, hs.1]
  · linarith [le_abs_self b, abs_nonneg a, hs.2]

theorem radial_slope_parts {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a b lo hi : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {G : ℝ × ℝ → ℂ} {C : NNReal} (hG : LipschitzOnWith C G (Icc a b ×ˢ Icc lo hi))
    (hGa : a = 0 → ∀ z ∈ Icc lo hi, G (a, z) = 0) :
    IntegrableOn (fun p => dF p * G p + F p * CellBox.radialDeriv G p) (Icc a b ×ˢ Icc lo hi) ∧
    ∫ p in Icc a b ×ˢ Icc lo hi, (dF p * G p + F p * CellBox.radialDeriv G p) =
      (∫ p in Icc a b ×ˢ Icc lo hi,
        ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.1 - a) / (b - a) : ℝ) : ℂ) * dF p) * G (b, p.2)) +
      ∫ p in Icc a b ×ˢ Icc lo hi,
        ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.1 - b) / (a - b) : ℝ) : ℂ) * dF p) * G (a, p.2) := by
  have hTm : MeasurableSet (Icc a b ×ˢ Icc lo hi) := measurableSet_Icc.prod measurableSet_Icc
  have hTc : IsCompact (Icc a b ×ˢ Icc lo hi) := isCompact_Icc.prod isCompact_Icc
  rcases lt_or_ge hi lo with hlh | hlh
  · have he : Icc a b ×ˢ Icc lo hi = (∅ : Set (ℝ × ℝ)) := by rw [Icc_eq_empty_of_lt hlh, prod_empty]
    simp [he]
  have hbT : ∀ z ∈ Icc lo hi, (b, z) ∈ Icc a b ×ˢ Icc lo hi := fun z hz => ⟨⟨hab.le, le_rfl⟩, hz⟩
  have haT : ∀ z ∈ Icc lo hi, (a, z) ∈ Icc a b ×ˢ Icc lo hi := fun z hz => ⟨⟨le_rfl, hab.le⟩, hz⟩
  have hside : ∀ v, (∀ z ∈ Icc lo hi, (v, z) ∈ Icc a b ×ˢ Icc lo hi) →
      LipschitzOnWith C (fun p : ℝ × ℝ => G (v, p.2)) (Icc a b ×ˢ Icc lo hi) := by
    intro v hv
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    refine (hG.dist_le_mul _ (hv _ hp.2) _ (hv _ hq.2)).trans (mul_le_mul_of_nonneg_left ?_ C.2)
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_le_max (by simp) le_rfl
  have hGb := hside b hbT
  have hGa' := hside a haT
  obtain ⟨M1, hM10, hM1⟩ := slope_bound_le hGb hTc
  obtain ⟨M2, hM20, hM2⟩ := slope_bound_le hGa' hTc
  obtain ⟨M3, hM30, hM3⟩ := slope_bound_le (ramp_slope_bound a (b - a) (Icc a b ×ˢ Icc lo hi)) hTc
  obtain ⟨M4, hM40, hM4⟩ := slope_bound_le (ramp_slope_bound b (a - b) (Icc a b ×ˢ Icc lo hi)) hTc
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × ℝ → ℂ, H = fun p => G p - (((p.1 - a) / (b - a) : ℝ) : ℂ) * G (b, p.2) -
      (((p.1 - b) / (a - b) : ℝ) : ℂ) * G (a, p.2) := ⟨_, rfl⟩
  have hHL := (hG.sub (slope_mul_bound (ramp_slope_bound a (b - a) _) hGb hM3 hM1 hM30 hM10)).sub
    (slope_mul_bound (ramp_slope_bound b (a - b) _) hGa' hM4 hM2 hM40 hM20)
  rw [← hHdef] at hHL
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab.ne
  have hHa : ∀ z ∈ Icc lo hi, H (a, z) = 0 := by
    intro z _
    rw [hHdef]
    simp only [sub_self, zero_div, div_self hab']
    push_cast; ring
  have hHb : ∀ z ∈ Icc lo hi, H (b, z) = 0 := by
    intro z _
    rw [hHdef]
    simp only [sub_self, zero_div, div_self hba]
    push_cast; ring
  obtain ⟨hI0, hE0⟩ := radial_slope_zero h ha hab hHL hHa hHb
  set Z := |lo| + |hi|
  have hF : IntegrableOn F (Icc a b ×ˢ Icc lo hi) :=
    (h.1 b Z).1.mono_set (prod_mono (Icc_subset_Icc_left ha) (box_sub' _ _))
  have hdFo : ∀ o c : ℝ, (a = 0 → o = 0) →
      IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) (Icc a b ×ˢ Icc lo hi) := by
    intro o c ho
    rcases ha.lt_or_eq with h0 | h0
    · have hd : IntegrableOn dF (Icc a b ×ˢ Icc lo hi) := (h.2.1 a b Z h0).mono_set (prod_mono subset_rfl (box_sub' _ _))
      exact IntegrableOn.continuousOn_mul (by fun_prop) hd hTc
    · have ho0 : o = 0 := ho h0.symm
      have hrd : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc a b ×ˢ Icc lo hi) :=
        (h.1 b Z).2.mono_set (prod_mono (Icc_subset_Icc_left ha) (box_sub' _ _))
      refine IntegrableOn.congr_fun (hrd.const_mul (((1 / (c - o) : ℝ)) : ℂ)) (fun p _ => ?_) hTm
      simp only [ho0, sub_zero]; push_cast; ring
  have hB : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.1 - a) / (b - a) : ℝ) : ℂ) * dF p) *
      G (b, p.2)) (Icc a b ×ˢ Icc lo hi) :=
    IntegrableOn.mul_continuousOn ((hF.const_mul _).add (hdFo a b (fun h0 => h0))) hGb.continuousOn hTc
  have hA : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.1 - b) / (a - b) : ℝ) : ℂ) * dF p) *
      G (a, p.2)) (Icc a b ×ˢ Icc lo hi) := by
    rcases ha.lt_or_eq with h0 | h0
    · exact IntegrableOn.mul_continuousOn ((hF.const_mul _).add (hdFo b a (fun e => absurd e h0.ne')))
        hGa'.continuousOn hTc
    · refine IntegrableOn.congr_fun (by exact integrableOn_zero : IntegrableOn (fun _ : ℝ × ℝ => (0 : ℂ)) (Icc a b ×ˢ Icc lo hi))
        (fun p hp => ?_) hTm
      simp [hGa h0.symm p.2 hp.2]
  have hae : ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)),
      dF p * G p + F p * CellBox.radialDeriv G p =
        (dF p * H p + F p * CellBox.radialDeriv H p) +
        ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.1 - a) / (b - a) : ℝ) : ℂ) * dF p) * G (b, p.2) +
        ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.1 - b) / (a - b) : ℝ) : ℂ) * dF p) * G (a, p.2) := by
    filter_upwards [ae_line_diff hab.le hlh hG] with p hp
    have r1 : HasDerivAt (fun r : ℝ => (((r - a) / (b - a) : ℝ) : ℂ)) (((1 / (b - a) : ℝ)) : ℂ) p.1 :=
      (((hasDerivAt_id p.1).sub_const a).div_const (b - a)).ofReal_comp
    have r2 : HasDerivAt (fun r : ℝ => (((r - b) / (a - b) : ℝ) : ℂ)) (((1 / (a - b) : ℝ)) : ℂ) p.1 :=
      (((hasDerivAt_id p.1).sub_const b).div_const (a - b)).ofReal_comp
    have hd : HasDerivAt (fun r => H (r, p.2)) (CellBox.radialDeriv G p - (((1 / (b - a) : ℝ)) : ℂ) * G (b, p.2) -
        (((1 / (a - b) : ℝ)) : ℂ) * G (a, p.2)) p.1 := by
      have h3 := (hp.hasDerivAt.sub (r1.mul_const (G (b, p.2)))).sub (r2.mul_const (G (a, p.2)))
      rw [hHdef]
      exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => rfl)
    have e : CellBox.radialDeriv H p = CellBox.radialDeriv G p - (((1 / (b - a) : ℝ)) : ℂ) * G (b, p.2) -
        (((1 / (a - b) : ℝ)) : ℂ) * G (a, p.2) := hd.deriv
    rw [e, hHdef]
    simp only
    ring
  refine ⟨((hI0.add hB).add hA).congr (hae.mono fun p hp => hp.symm), ?_⟩
  rw [integral_congr_ae hae]
  have s1 := integral_add (hI0.add hB) hA
  have s2 := integral_add hI0 hB
  simp only [Pi.add_apply] at s1 s2
  rw [s1, s2, hE0, zero_add]

theorem height_slope_parts {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {lo hi a b : ℝ}
    (hlo : 0 ≤ lo) (hab : a < b) {G : ℝ × ℝ → ℂ} {C : NNReal} (hG : LipschitzOnWith C G (Icc lo hi ×ˢ Icc a b)) :
    IntegrableOn (fun p => (p.1 : ℂ) * (dF p * G p + F p * CellBox.heightDeriv G p)) (Icc lo hi ×ˢ Icc a b) ∧
    ∫ p in Icc lo hi ×ˢ Icc a b, (p.1 : ℂ) * (dF p * G p + F p * CellBox.heightDeriv G p) =
      (∫ p in Icc lo hi ×ˢ Icc a b,
        ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * G (p.1, b))) +
      ∫ p in Icc lo hi ×ˢ Icc a b,
        ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.2 - b) / (a - b) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * G (p.1, a)) := by
  have hTm : MeasurableSet (Icc lo hi ×ˢ Icc a b) := measurableSet_Icc.prod measurableSet_Icc
  have hTc : IsCompact (Icc lo hi ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  rcases lt_or_ge hi lo with hlh | hlh
  · have he : Icc lo hi ×ˢ Icc a b = (∅ : Set (ℝ × ℝ)) := by rw [Icc_eq_empty_of_lt hlh, empty_prod]
    simp [he]
  have hbT : ∀ r ∈ Icc lo hi, (r, b) ∈ Icc lo hi ×ˢ Icc a b := fun r hr => ⟨hr, ⟨hab.le, le_rfl⟩⟩
  have haT : ∀ r ∈ Icc lo hi, (r, a) ∈ Icc lo hi ×ˢ Icc a b := fun r hr => ⟨hr, ⟨le_rfl, hab.le⟩⟩
  have hside : ∀ v, (∀ r ∈ Icc lo hi, (r, v) ∈ Icc lo hi ×ˢ Icc a b) →
      LipschitzOnWith C (fun p : ℝ × ℝ => G (p.1, v)) (Icc lo hi ×ˢ Icc a b) := by
    intro v hv
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    refine (hG.dist_le_mul _ (hv _ hp.1) _ (hv _ hq.1)).trans (mul_le_mul_of_nonneg_left ?_ C.2)
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_le_max le_rfl (by simp)
  have hGb := hside b hbT
  have hGa' := hside a haT
  obtain ⟨M1, hM10, hM1⟩ := slope_bound_le hGb hTc
  obtain ⟨M2, hM20, hM2⟩ := slope_bound_le hGa' hTc
  obtain ⟨M3, hM30, hM3⟩ := slope_bound_le (ramp2_slope_bound a (b - a) (Icc lo hi ×ˢ Icc a b)) hTc
  obtain ⟨M4, hM40, hM4⟩ := slope_bound_le (ramp2_slope_bound b (a - b) (Icc lo hi ×ˢ Icc a b)) hTc
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × ℝ → ℂ, H = fun p => G p - (((p.2 - a) / (b - a) : ℝ) : ℂ) * G (p.1, b) -
      (((p.2 - b) / (a - b) : ℝ) : ℂ) * G (p.1, a) := ⟨_, rfl⟩
  have hHL := (hG.sub (slope_mul_bound (ramp2_slope_bound a (b - a) _) hGb hM3 hM1 hM30 hM10)).sub
    (slope_mul_bound (ramp2_slope_bound b (a - b) _) hGa' hM4 hM2 hM40 hM20)
  rw [← hHdef] at hHL
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab.ne
  have hHa : ∀ r ∈ Icc lo hi, H (r, a) = 0 := by
    intro r _
    rw [hHdef]
    simp only [sub_self, zero_div, div_self hab']
    push_cast; ring
  have hHb : ∀ r ∈ Icc lo hi, H (r, b) = 0 := by
    intro r _
    rw [hHdef]
    simp only [sub_self, zero_div, div_self hba]
    push_cast; ring
  obtain ⟨hI0, hE0⟩ := height_slope_zero h hlo hab hHL hHa hHb
  have hbox : Icc lo hi ×ˢ Icc a b ⊆ Icc (-(|lo| + |hi|)) (|lo| + |hi|) ×ˢ Icc (-(|a| + |b|)) (|a| + |b|) :=
    prod_mono (box_sub' _ _) (box_sub' _ _)
  have hF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc lo hi ×ˢ Icc a b) := (h.1 _ _).1.mono_set hbox
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc lo hi ×ˢ Icc a b) := (h.1 _ _).2.mono_set hbox
  have hW : ∀ (c o : ℝ) (g : ℝ × ℝ → ℂ), ContinuousOn g (Icc lo hi ×ˢ Icc a b) →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
        ((p.1 : ℂ) * g p)) (Icc lo hi ×ˢ Icc a b) := by
    intro c o g hg
    have h1 : IntegrableOn (fun p : ℝ × ℝ => (((((1 / (c - o) : ℝ)) : ℂ) * ((p.1 : ℂ) * F p)) +
        (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((p.1 : ℂ) * dF p)) * g p) (Icc lo hi ×ˢ Icc a b) :=
      IntegrableOn.mul_continuousOn ((hF.const_mul _).add (IntegrableOn.continuousOn_mul
        (show Continuous fun p : ℝ × ℝ => ((((p.2 - o) / (c - o) : ℝ)) : ℂ) by fun_prop).continuousOn hdF hTc))
        hg hTc
    exact h1.congr_fun (fun p _ => by ring) hTm
  have hB := hW b a _ hGb.continuousOn
  have hA := hW a b _ hGa'.continuousOn
  have hae : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)),
      (p.1 : ℂ) * (dF p * G p + F p * CellBox.heightDeriv G p) =
        (p.1 : ℂ) * (dF p * H p + F p * CellBox.heightDeriv H p) +
        ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * G (p.1, b)) +
        ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.2 - b) / (a - b) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * G (p.1, a)) := by
    filter_upwards [ae_line_diff2 hlh hab.le hG] with p hp
    have r1 : HasDerivAt (fun z : ℝ => (((z - a) / (b - a) : ℝ) : ℂ)) (((1 / (b - a) : ℝ)) : ℂ) p.2 :=
      (((hasDerivAt_id p.2).sub_const a).div_const (b - a)).ofReal_comp
    have r2 : HasDerivAt (fun z : ℝ => (((z - b) / (a - b) : ℝ) : ℂ)) (((1 / (a - b) : ℝ)) : ℂ) p.2 :=
      (((hasDerivAt_id p.2).sub_const b).div_const (a - b)).ofReal_comp
    have hd : HasDerivAt (fun z => H (p.1, z)) (CellBox.heightDeriv G p - (((1 / (b - a) : ℝ)) : ℂ) * G (p.1, b) -
        (((1 / (a - b) : ℝ)) : ℂ) * G (p.1, a)) p.2 := by
      have h3 := (hp.hasDerivAt.sub (r1.mul_const (G (p.1, b)))).sub (r2.mul_const (G (p.1, a)))
      rw [hHdef]
      exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => rfl)
    have e : CellBox.heightDeriv H p = CellBox.heightDeriv G p - (((1 / (b - a) : ℝ)) : ℂ) * G (p.1, b) -
        (((1 / (a - b) : ℝ)) : ℂ) * G (p.1, a) := hd.deriv
    rw [e, hHdef]
    simp only
    ring
  refine ⟨((hI0.add hB).add hA).congr (hae.mono fun p hp => hp.symm), ?_⟩
  rw [integral_congr_ae hae]
  have s1 := integral_add (hI0.add hB) hA
  have s2 := integral_add hI0 hB
  simp only [Pi.add_apply] at s1 s2
  rw [s1, s2, hE0, zero_add]

end Breakdown.FracInternal.LayoutRowPressureSideCore
