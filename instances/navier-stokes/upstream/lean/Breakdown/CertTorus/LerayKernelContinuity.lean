import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.FarField

namespace Internal

private theorem coordIf_continuous (c : Prop) [Decidable c] (i : Fin 3) :
    Continuous (fun q : ℝ × Space => if c then q.2 i else 0) :=
  continuous_if_const c (fun _ => by fun_prop) (fun _ => continuous_const)

private theorem heatKernel_measurable_prod :
    Measurable (fun q : ℝ × Space => heatKernel q.1 q.2) := by
  unfold heatKernel
  fun_prop

private theorem heatKernelThird_measurable_prod (i j k : Fin 3) :
    Measurable (fun q : ℝ × Space => heatKernelThird i j k q.1 q.2) := by
  unfold heatKernelThird
  have h1 := (coordIf_continuous (j = k) i).measurable
  have h2 := (coordIf_continuous (i = k) j).measurable
  have h3 := (coordIf_continuous (i = j) k).measurable
  have hH := heatKernel_measurable_prod
  fun_prop

private theorem heatKernel_continuousAt_prod {ρ : ℝ} (hρ : ρ ≠ 0) (x : Space) :
    ContinuousAt (fun q : ℝ × Space => heatKernel q.1 q.2) (ρ, x) := by
  unfold heatKernel
  have h4 : 4 * π * ρ ≠ 0 := mul_ne_zero (by positivity) hρ
  have h4' : 4 * ρ ≠ 0 := mul_ne_zero (by norm_num) hρ
  apply ContinuousAt.mul
  · exact ContinuousAt.rpow_const (by fun_prop) (Or.inl h4)
  · exact Real.continuous_exp.continuousAt.comp
      (ContinuousAt.div (by fun_prop) (by fun_prop) h4')

private theorem heatKernelThird_continuousAt_prod (i j k : Fin 3) {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : Space) :
    ContinuousAt (fun q : ℝ × Space => heatKernelThird i j k q.1 q.2) (ρ, x) := by
  unfold heatKernelThird
  have h1 := (coordIf_continuous (j = k) i).continuousAt (x := (ρ, x))
  have h2 := (coordIf_continuous (i = k) j).continuousAt (x := (ρ, x))
  have h3 := (coordIf_continuous (i = j) k).continuousAt (x := (ρ, x))
  have hH := heatKernel_continuousAt_prod hρ x
  have hd2 : 4 * ρ ^ 2 ≠ 0 := by positivity
  have hd3 : 8 * ρ ^ 3 ≠ 0 := by positivity
  apply ContinuousAt.sub
  · exact ((h1.add h2).add h3).div (by fun_prop) hd2 |>.mul hH
  · have hq : ContinuousAt (fun q : ℝ × Space => q.2 i * q.2 j * q.2 k / (8 * q.1 ^ 3)) (ρ, x) :=
      ContinuousAt.div (by fun_prop) (by fun_prop) hd3
    exact hq.mul hH

private theorem lerayKernel_measurable_all : LerayKernelMeasurable := by
  intro i j k
  have hA : Measurable (fun p : ℝ × Space =>
      if i = j then -(p.2 k / (2 * p.1)) * heatKernel p.1 p.2 else 0) := by
    by_cases h : i = j
    · simp only [h, if_true]
      have hH := heatKernel_measurable_prod
      fun_prop
    · simp only [h, if_false]
      exact measurable_const
  have hF : StronglyMeasurable (fun q : (ℝ × Space) × ℝ =>
      (Ioi q.1.1).indicator (fun ρ => heatKernelThird i j k ρ q.1.2) q.2) := by
    apply Measurable.stronglyMeasurable
    have e : (fun q : (ℝ × Space) × ℝ =>
        (Ioi q.1.1).indicator (fun ρ => heatKernelThird i j k ρ q.1.2) q.2) =
        fun q => if q.1.1 < q.2 then heatKernelThird i j k q.2 q.1.2 else 0 := by
      funext q
      simp only [Set.indicator, mem_Ioi]
    rw [e]
    refine Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) ?_ measurable_const
    have hm : Measurable (fun q : (ℝ × Space) × ℝ => (q.2, q.1.2)) := by fun_prop
    exact (heatKernelThird_measurable_prod i j k).comp hm
  have hB : Measurable (fun p : ℝ × Space => ∫ ρ in Ioi p.1, heatKernelThird i j k ρ p.2) := by
    have e : (fun p : ℝ × Space => ∫ ρ in Ioi p.1, heatKernelThird i j k ρ p.2) =
        fun p => ∫ ρ, (Ioi p.1).indicator (fun ρ => heatKernelThird i j k ρ p.2) ρ := by
      funext p
      rw [integral_indicator measurableSet_Ioi]
    rw [e]
    exact (hF.integral_prod_right' (ν := volume)).measurable
  exact hA.add hB

private theorem heatKernelThird_le_cube {C : ℝ}
    (hC : ∀ τ : ℝ, 0 < τ → ∀ x : Space,
      heatKernel τ x ≤ C / (‖x‖ + Real.sqrt τ) ^ 3 ∧
      (∀ k : Fin 3, |x k / (2 * τ) * heatKernel τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4) ∧
      ∀ i j k : Fin 3, |heatKernelThird i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 6)
    (i j k : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) (x : Space) :
    |heatKernelThird i j k ρ x| ≤ C / ρ ^ 3 := by
  have hC0 : 0 ≤ C := by
    have h := (hC 1 one_pos x).2.2 i j k
    have hpos : 0 < (‖x‖ + Real.sqrt 1) ^ 6 := by positivity
    have := (abs_nonneg _).trans h
    exact (div_nonneg_iff.mp this).elim (fun h' => h'.1) (fun h' => absurd h'.2 (not_le.mpr hpos))
  have hs : Real.sqrt ρ ^ 6 = ρ ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt hρ.le]
  have hle : ρ ^ 3 ≤ (‖x‖ + Real.sqrt ρ) ^ 6 := by
    rw [← hs]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) 6
  exact ((hC ρ hρ x).2.2 i j k).trans (div_le_div_of_nonneg_left hC0 (by positivity) hle)

private theorem lerayKernel_jointContinuous_of_bounds (hHB : HeatKernelBounds) :
    LerayKernelJointContinuous := by
  obtain ⟨C, hC⟩ := hHB
  have hC0 : 0 ≤ C := by
    have h := heatKernelThird_le_cube hC 0 0 0 one_pos 0
    have := (abs_nonneg _).trans h
    simpa using this
  intro i j k
  refine continuousOn_of_forall_continuousAt fun p0 hp0 => ?_
  have hτ0 : 0 < p0.1 := hp0.1
  have hA : ContinuousAt (fun p : ℝ × Space =>
      if i = j then -(p.2 k / (2 * p.1)) * heatKernel p.1 p.2 else 0) p0 := by
    by_cases h : i = j
    · simp only [h, if_true]
      have hH := heatKernel_continuousAt_prod hτ0.ne' p0.2
      have h2 : 2 * p0.1 ≠ 0 := by positivity
      have hq : ContinuousAt (fun p : ℝ × Space => p.2 k / (2 * p.1)) p0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) h2
      exact hq.neg.mul hH
    · simp only [h, if_false]
      exact continuousAt_const
  have hB : ContinuousAt (fun p : ℝ × Space =>
      p.1 * ∫ t in Ioi (1 : ℝ), heatKernelThird i j k (p.1 * t) p.2) p0 := by
    refine continuousAt_fst.mul ?_
    refine continuousAt_of_dominated (bound := fun t : ℝ => C * (8 / p0.1 ^ 3) * t ^ (-3 : ℝ)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun p => ?_
      have hm : Measurable (fun t : ℝ => (p.1 * t, p.2)) := by fun_prop
      exact ((heatKernelThird_measurable_prod i j k).comp hm).aestronglyMeasurable
    · filter_upwards [(continuous_fst.tendsto p0).eventually (lt_mem_nhds (half_lt_self hτ0))]
        with p hp
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun t ht => ?_
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      have hpt : 0 < p.1 * t := mul_pos (lt_trans (half_pos hτ0) hp) ht0
      rw [Real.norm_eq_abs]
      refine (heatKernelThird_le_cube hC i j k hpt p.2).trans ?_
      have hlow : p0.1 ^ 3 * t ^ 3 / 8 ≤ (p.1 * t) ^ 3 := by
        have : p0.1 / 2 * t ≤ p.1 * t := mul_le_mul_of_nonneg_right hp.le ht0.le
        calc p0.1 ^ 3 * t ^ 3 / 8 = (p0.1 / 2 * t) ^ 3 := by ring
          _ ≤ (p.1 * t) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
      have hrp : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
        rw [Real.rpow_neg ht0.le]
        norm_cast
      rw [hrp]
      calc C / (p.1 * t) ^ 3 ≤ C / (p0.1 ^ 3 * t ^ 3 / 8) :=
            div_le_div_of_nonneg_left hC0 (by positivity) hlow
        _ = C * (8 / p0.1 ^ 3) * (t ^ 3)⁻¹ := by
            field_simp
    · have hi : Integrable (fun t : ℝ => t ^ (-3 : ℝ)) (volume.restrict (Ioi 1)) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
      exact hi.const_mul (C * (8 / p0.1 ^ 3))
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun t ht => ?_
      have hne : p0.1 * t ≠ 0 := (mul_pos hτ0 (lt_trans one_pos ht)).ne'
      have hg : ContinuousAt (fun p : ℝ × Space => (p.1 * t, p.2)) p0 := by fun_prop
      exact ContinuousAt.comp_of_eq (heatKernelThird_continuousAt_prod i j k hne p0.2) hg rfl
  have heq : (fun p : ℝ × Space =>
      p.1 * ∫ t in Ioi (1 : ℝ), heatKernelThird i j k (p.1 * t) p.2) =ᶠ[𝓝 p0]
      fun p => ∫ ρ in Ioi p.1, heatKernelThird i j k ρ p.2 := by
    filter_upwards [(continuous_fst.tendsto p0).eventually (lt_mem_nhds hτ0)] with p hp
    rw [integral_comp_mul_left_Ioi (fun ρ => heatKernelThird i j k ρ p.2) 1 hp, smul_eq_mul,
      mul_one, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  exact hA.add (hB.congr heq)

end Internal

theorem lerayKernel_continuous_measurable :
    HeatKernelBounds → LerayKernelJointContinuous ∧ LerayKernelMeasurable :=
  fun h => ⟨Internal.lerayKernel_jointContinuous_of_bounds h, Internal.lerayKernel_measurable_all⟩

end Breakdown.FarField
