import Breakdown.Torus.HeatComparisonStatements

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace PartitionSum.Internal

theorem freq_coord (k : Lattice) (i : Fin 3) : (freq k) i = (k i : ℝ) := by
  simp [freq, unitVector, Pi.single_apply]

theorem norm_sub_step_le {h : ℝ} (hh : 0 < h) (ξ : Space) :
    ‖ξ - h • freq (latticeIndex h ξ)‖ ≤ 2 * h := by
  have hc : ∀ j, ‖(ξ - h • freq (latticeIndex h ξ)) j‖ ≤ h := by
    intro j
    have e : (ξ - h • freq (latticeIndex h ξ)) j = ξ j - h * (⌊ξ j / h⌋ : ℝ) := by
      simp [freq_coord, latticeIndex]
    rw [e, Real.norm_eq_abs, abs_le]
    have h1 := Int.floor_le (ξ j / h)
    have h2 := Int.lt_floor_add_one (ξ j / h)
    have h3 : h * (ξ j / h) = ξ j := by field_simp
    constructor
    · nlinarith
    · nlinarith
  have hsq : ‖ξ - h • freq (latticeIndex h ξ)‖ ^ 2 ≤ (2 * h) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have a0 := pow_le_pow_left₀ (norm_nonneg _) (hc 0) 2
    have a1 := pow_le_pow_left₀ (norm_nonneg _) (hc 1) 2
    have a2 := pow_le_pow_left₀ (norm_nonneg _) (hc 2) 2
    nlinarith [sq_nonneg h]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

theorem decay_le_of_near {ξ ξ' : Space} (hn : ‖ξ - ξ'‖ ≤ 2) :
    (1 + ‖ξ'‖) ^ (-4 : ℝ) ≤ 81 * (1 + ‖ξ‖) ^ (-4 : ℝ) := by
  have hx : 0 < 1 + ‖ξ‖ := by positivity
  have hy : 0 < 1 + ‖ξ'‖ := by positivity
  have htri : ‖ξ‖ ≤ ‖ξ'‖ + 2 := by
    have := norm_sub_norm_le ξ ξ'
    linarith
  have hle : 1 + ‖ξ‖ ≤ 3 * (1 + ‖ξ'‖) := by linarith [norm_nonneg ξ']
  have e : ∀ t : ℝ, 0 < t → t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by
    intro t ht
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]
  rw [e _ hx, e _ hy]
  have hp : (1 + ‖ξ‖) ^ 4 ≤ 81 * (1 + ‖ξ'‖) ^ 4 := by
    calc (1 + ‖ξ‖) ^ 4 ≤ (3 * (1 + ‖ξ'‖)) ^ 4 := by gcongr
      _ = 81 * (1 + ‖ξ'‖) ^ 4 := by ring
  have hb : 0 < (1 + ‖ξ'‖) ^ 4 := by positivity
  calc ((1 + ‖ξ'‖) ^ 4)⁻¹ = 81 * (81 * (1 + ‖ξ'‖) ^ 4)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num), one_mul]
    _ ≤ 81 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by gcongr

theorem continuousOn_of_slope {g : Space → Coef}
    (hL : ∀ r R : ℝ, 0 < r → ∃ L : ℝ, ∀ ξ ξ' : Space, r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖g ξ - g ξ'‖ ≤ L * ‖ξ - ξ'‖) : ContinuousOn g {0}ᶜ := by
  intro ξ₀ hξ₀
  have hρ : 0 < ‖ξ₀‖ := norm_pos_iff.2 hξ₀
  obtain ⟨L, hL⟩ := hL (‖ξ₀‖ / 2) (2 * ‖ξ₀‖) (by positivity)
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have ht : Tendsto (fun ξ : Space => max L 0 * ‖ξ - ξ₀‖) (𝓝 ξ₀) (𝓝 0) := by
    have : Tendsto (fun ξ : Space => ‖ξ - ξ₀‖) (𝓝 ξ₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 tendsto_id
    simpa using this.const_mul (max L 0)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  have hball : ∀ᶠ ξ in 𝓝 ξ₀, ‖ξ - ξ₀‖ < ‖ξ₀‖ / 2 := by
    filter_upwards [Metric.ball_mem_nhds ξ₀ (half_pos hρ)] with ξ hξ
    rwa [Metric.mem_ball, dist_eq_norm] at hξ
  filter_upwards [hball] with ξ hξ
  have a1 := norm_sub_norm_le ξ ξ₀
  have a2 := norm_sub_norm_le ξ₀ ξ
  rw [norm_sub_rev ξ₀ ξ] at a2
  calc ‖g ξ - g ξ₀‖ ≤ L * ‖ξ - ξ₀‖ :=
        hL ξ ξ₀ (by linarith) (by linarith) (by linarith) (by linarith)
    _ ≤ max L 0 * ‖ξ - ξ₀‖ := by gcongr; exact le_max_left _ _

theorem aestronglyMeasurable_of_slope {g : Space → Coef}
    (hL : ∀ r R : ℝ, 0 < r → ∃ L : ℝ, ∀ ξ ξ' : Space, r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖g ξ - g ξ'‖ ≤ L * ‖ξ - ξ'‖) : AEStronglyMeasurable g (volume : Measure Space) := by
  have := (continuousOn_of_slope hL).aestronglyMeasurable (μ := (volume : Measure Space))
    (measurableSet_singleton (0 : Space)).compl
  rwa [restrict_compl_singleton] at this

theorem integrable_decay : Integrable (fun ξ : Space => (1 + ‖ξ‖) ^ (-4 : ℝ)) := by
  apply integrable_one_add_norm
  rw [finrank_euclideanSpace_fin]
  norm_num

def annulus (n : ℕ) : Set Space := {ξ | ((n : ℝ) + 1)⁻¹ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (n : ℝ) + 1}

theorem mem_annulus {n : ℕ} {ξ : Space} :
    ξ ∈ annulus n ↔ ((n : ℝ) + 1)⁻¹ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (n : ℝ) + 1 := Iff.rfl

theorem measurableSet_annulus (n : ℕ) : MeasurableSet (annulus n) :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

theorem exists_tail_le {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ,
    ∫ ξ in (annulus n)ᶜ, (1 + ‖ξ‖) ^ (-4 : ℝ) ≤ ε := by
  have hmono : Monotone annulus := by
    intro n m hnm ξ hξ
    rw [mem_annulus] at hξ ⊢
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
    refine ⟨le_trans ?_ hξ.1, hξ.2.trans (by linarith)⟩
    gcongr
  have hU : (⋃ n, annulus n) = {0}ᶜ := by
    ext ξ
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff, mem_annulus]
    constructor
    · rintro ⟨n, h1, -⟩ rfl
      rw [norm_zero] at h1
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    · intro hξ
      have hρ : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      obtain ⟨n, hn⟩ := exists_nat_gt (max ‖ξ‖ ‖ξ‖⁻¹)
      refine ⟨n, ?_, ?_⟩
      · rw [inv_le_comm₀ (by positivity) hρ]
        linarith [le_max_right ‖ξ‖ ‖ξ‖⁻¹]
      · linarith [le_max_left ‖ξ‖ ‖ξ‖⁻¹]
  have ht := tendsto_setIntegral_of_monotone (μ := (volume : Measure Space))
    (f := fun ξ : Space => (1 + ‖ξ‖) ^ (-4 : ℝ)) measurableSet_annulus hmono
    integrable_decay.integrableOn
  rw [hU, restrict_compl_singleton] at ht
  have ht2 : Tendsto (fun n => ∫ ξ in (annulus n)ᶜ, (1 + ‖ξ‖) ^ (-4 : ℝ)) atTop (𝓝 0) := by
    have e : ∀ n : ℕ, ∫ ξ in (annulus n)ᶜ, (1 + ‖ξ‖) ^ (-4 : ℝ) =
        (∫ ξ : Space, (1 + ‖ξ‖) ^ (-4 : ℝ)) - ∫ ξ in annulus n, (1 + ‖ξ‖) ^ (-4 : ℝ) := by
      intro n
      rw [← integral_add_compl (measurableSet_annulus n) integrable_decay]
      ring
    simp_rw [e]
    simpa using (tendsto_const_nhds (x := ∫ ξ : Space, (1 + ‖ξ‖) ^ (-4 : ℝ))).sub ht
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht2).2 ε hε).exists
  exact ⟨n, hn.le⟩

theorem mul_div_two_succ_le {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    c * (δ / (2 * (c + 1))) ≤ δ / 2 := by
  have hc1 : 0 < c + 1 := by linarith
  have e : c * (δ / (2 * (c + 1))) = δ / 2 - δ / (2 * (c + 1)) := by
    field_simp
    ring
  have : 0 < δ / (2 * (c + 1)) := by positivity
  linarith

end PartitionSum.Internal

open PartitionSum.Internal in
theorem partitionSumBound_of_step (hS : StepIntegral) : PartitionSumBound := by
  intro ι G K hK hSlope δ hδ
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hG : ∀ i ξ, ‖G i ξ‖ ≤ max K 0 * (1 + ‖ξ‖) ^ (-4 : ℝ) := fun i ξ =>
    (hK i ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨n, hn⟩ := exists_tail_le (ε := δ / (2 * (82 * max K 0 + 1))) (by positivity)
  obtain ⟨L, hL⟩ := hSlope ((2 * ((n : ℝ) + 1))⁻¹) ((n : ℝ) + 2) (by positivity)
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  have hVpos : 0 ≤ (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) :=
    measureReal_nonneg
  refine ⟨min (min (1 / 2) (4 * ((n : ℝ) + 1))⁻¹)
    (δ / (2 * (2 * max L 0 * (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) + 1))),
    by positivity, ?_⟩
  intro h hh hh0 i
  have h1 : h ≤ 1 / 2 := by
    have := min_le_left (min (1 / 2) (4 * ((n : ℝ) + 1))⁻¹) (δ / (2 * (2 * max L 0 *
      (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) + 1)))
    have := min_le_left (1 / 2 : ℝ) (4 * ((n : ℝ) + 1))⁻¹
    linarith
  have h2 : h ≤ (4 * ((n : ℝ) + 1))⁻¹ := by
    have := min_le_left (min (1 / 2) (4 * ((n : ℝ) + 1))⁻¹) (δ / (2 * (2 * max L 0 *
      (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) + 1)))
    have := min_le_right (1 / 2 : ℝ) (4 * ((n : ℝ) + 1))⁻¹
    linarith
  have h3 : h ≤ δ / (2 * (2 * max L 0 *
      (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) + 1)) := by
    have := min_le_right (min (1 / 2) (4 * ((n : ℝ) + 1))⁻¹) (δ / (2 * (2 * max L 0 *
      (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) + 1)))
    linarith
  obtain ⟨-, hS2, hS3⟩ := hS h hh
  have hsum : Summable (fun k => ‖G i (h • freq k)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hG i _) (hS3.mul_left (max K 0))
  obtain ⟨hint, heq⟩ := hS2 (fun k => G i (h • freq k)) hsum
  have heq' : latticeSum h (G i) = ∫ ξ, G i (h • freq (latticeIndex h ξ)) := by
    rw [latticeSum]
    exact heq.symm
  have hGint : Integrable (G i) :=
    (integrable_decay.const_mul (max K 0)).mono'
      (aestronglyMeasurable_of_slope (fun r R hr => by
        obtain ⟨L₁, hL₁⟩ := hSlope r R hr
        exact ⟨L₁, fun ξ ξ' => hL₁ i ξ ξ'⟩))
      (Eventually.of_forall (hG i))
  have hint' : Integrable (fun ξ => G i (h • freq (latticeIndex h ξ))) := hint
  have hf_int : Integrable (fun ξ => ‖G i (h • freq (latticeIndex h ξ)) - G i ξ‖) :=
    (hint'.sub hGint).norm
  have hB_int : Integrable (fun ξ : Space =>
      (Metric.closedBall (0 : Space) ((n : ℝ) + 1)).indicator (fun _ => 2 * max L 0 * h) ξ +
        82 * max K 0 * (annulus n)ᶜ.indicator (fun ξ => (1 + ‖ξ‖) ^ (-4 : ℝ)) ξ) := by
    refine Integrable.add ?_ ?_
    · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
    · exact (integrable_decay.indicator (measurableSet_annulus n).compl).const_mul _
  have key : ∀ ξ, ‖G i (h • freq (latticeIndex h ξ)) - G i ξ‖ ≤
      (Metric.closedBall (0 : Space) ((n : ℝ) + 1)).indicator (fun _ => 2 * max L 0 * h) ξ +
        82 * max K 0 * (annulus n)ᶜ.indicator (fun ξ => (1 + ‖ξ‖) ^ (-4 : ℝ)) ξ := by
    intro ξ
    have hd := norm_sub_step_le hh ξ
    by_cases hE : ξ ∈ annulus n
    · have hE' := mem_annulus.1 hE
      have hball : ξ ∈ Metric.closedBall (0 : Space) ((n : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff]
        exact hE'.2
      rw [Set.indicator_of_mem hball, Set.indicator_of_notMem (s := (annulus n)ᶜ) (fun hc => hc hE), mul_zero,
        add_zero]
      have a1 := norm_sub_norm_le ξ (ξ - h • freq (latticeIndex h ξ))
      have a2 := norm_sub_norm_le (h • freq (latticeIndex h ξ)) ξ
      rw [sub_sub_cancel] at a1
      rw [norm_sub_rev] at a2
      have ei : (2 * ((n : ℝ) + 1))⁻¹ = ((n : ℝ) + 1)⁻¹ / 2 := by rw [mul_inv]; ring
      have ei' : (4 * ((n : ℝ) + 1))⁻¹ = ((n : ℝ) + 1)⁻¹ / 4 := by rw [mul_inv]; ring
      rw [ei'] at h2
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc ‖G i (h • freq (latticeIndex h ξ)) - G i ξ‖
          ≤ L * ‖h • freq (latticeIndex h ξ) - ξ‖ :=
            hL i _ _ (by rw [ei]; linarith) (by linarith) (by rw [ei]; linarith) (by linarith)
        _ ≤ max L 0 * ‖h • freq (latticeIndex h ξ) - ξ‖ := by
            gcongr
            exact le_max_left _ _
        _ ≤ max L 0 * (2 * h) := by
            gcongr
            rw [norm_sub_rev]
            exact hd
        _ = 2 * max L 0 * h := by ring
    · rw [Set.indicator_of_mem (s := (annulus n)ᶜ) hE]
      have hnn : 0 ≤ (Metric.closedBall (0 : Space) ((n : ℝ) + 1)).indicator
          (fun _ => 2 * max L 0 * h) ξ :=
        Set.indicator_nonneg (fun _ _ => by positivity) ξ
      have hw := decay_le_of_near (ξ := ξ) (ξ' := h • freq (latticeIndex h ξ)) (by linarith)
      have hD0 : 0 ≤ (1 + ‖ξ‖) ^ (-4 : ℝ) := by positivity
      calc ‖G i (h • freq (latticeIndex h ξ)) - G i ξ‖
          ≤ ‖G i (h • freq (latticeIndex h ξ))‖ + ‖G i ξ‖ := norm_sub_le _ _
        _ ≤ max K 0 * (1 + ‖h • freq (latticeIndex h ξ)‖) ^ (-4 : ℝ) +
            max K 0 * (1 + ‖ξ‖) ^ (-4 : ℝ) := add_le_add (hG i _) (hG i _)
        _ ≤ max K 0 * (81 * (1 + ‖ξ‖) ^ (-4 : ℝ)) + max K 0 * (1 + ‖ξ‖) ^ (-4 : ℝ) := by
            gcongr
        _ = 82 * max K 0 * (1 + ‖ξ‖) ^ (-4 : ℝ) := by ring
        _ ≤ _ := by linarith
  have hcalc : ∫ ξ : Space,
      ((Metric.closedBall (0 : Space) ((n : ℝ) + 1)).indicator (fun _ => 2 * max L 0 * h) ξ +
        82 * max K 0 * (annulus n)ᶜ.indicator (fun ξ => (1 + ‖ξ‖) ^ (-4 : ℝ)) ξ) =
      (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) * (2 * max L 0 * h) +
        82 * max K 0 * ∫ ξ in (annulus n)ᶜ, (1 + ‖ξ‖) ^ (-4 : ℝ) := by
    rw [integral_add
        ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
          Metric.isClosed_closedBall.measurableSet)
        ((integrable_decay.indicator (measurableSet_annulus n).compl).const_mul _),
      integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, integral_const_mul,
      integral_indicator (measurableSet_annulus n).compl, smul_eq_mul]
  have hA : (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) *
      (2 * max L 0 * h) ≤ δ / 2 := by
    calc (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) * (2 * max L 0 * h)
        = (2 * max L 0 * (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1))) * h := by
          ring
      _ ≤ (2 * max L 0 * (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1))) *
          (δ / (2 * (2 * max L 0 *
            (volume : Measure Space).real (Metric.closedBall 0 ((n : ℝ) + 1)) + 1))) := by
          gcongr
      _ ≤ δ / 2 := mul_div_two_succ_le (by positivity) hδ
  have hB : 82 * max K 0 * ∫ ξ in (annulus n)ᶜ, (1 + ‖ξ‖) ^ (-4 : ℝ) ≤ δ / 2 := by
    calc 82 * max K 0 * ∫ ξ in (annulus n)ᶜ, (1 + ‖ξ‖) ^ (-4 : ℝ)
        ≤ 82 * max K 0 * (δ / (2 * (82 * max K 0 + 1))) := by gcongr
      _ ≤ δ / 2 := mul_div_two_succ_le (by positivity) hδ
  calc ‖latticeSum h (G i) - ∫ ξ, G i ξ‖
      = ‖∫ ξ, (G i (h • freq (latticeIndex h ξ)) - G i ξ)‖ := by
        rw [heq', integral_sub hint' hGint]
    _ ≤ ∫ ξ, ‖G i (h • freq (latticeIndex h ξ)) - G i ξ‖ := norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono hf_int hB_int key
    _ = _ := hcalc
    _ ≤ δ / 2 + δ / 2 := add_le_add hA hB
    _ = δ := by ring

end Breakdown.Periodic
