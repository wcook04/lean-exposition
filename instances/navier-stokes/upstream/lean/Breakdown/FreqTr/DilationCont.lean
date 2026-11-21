import Breakdown.FreqTr.Statements

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.DilationCont

open Metric

def scaleOp (c : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp (fun ξ => c • ξ) (fun _ => c • ContinuousLinearMap.id ℝ CSpace)

def scaleEquiv (c : ℝ) (hc : c ≠ 0) : Space ≃L[ℝ] Space :=
  (LinearEquiv.smulOfNeZero ℝ Space c hc).toContinuousLinearEquiv

theorem scaleOp_realized (h1 : FieldOpRealized) {c : ℝ} (hc : c ≠ 0) (f : L2C) :
    (scaleOp c f : Space → CSpace) =ᵐ[volume] fun ξ => c • f (c • ξ) := by
  have := h1 (scaleEquiv c hc) (fun _ => c • ContinuousLinearMap.id ℝ CSpace) |c|
    aestronglyMeasurable_const (fun _ => by
      refine (norm_smul_le _ _).trans ?_
      simp [Real.norm_eq_abs])
  exact this f

theorem eLpNorm_comp_smul {c : ℝ} (hc : 0 < c) (g : Space → CSpace)
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun ξ => g (c • ξ)) 2 volume =
      ENNReal.ofReal (c ^ 3)⁻¹ ^ (1 / 2 : ℝ) * eLpNorm g 2 volume := by
  have hmap := Measure.map_addHaar_smul (volume : Measure Space) hc.ne'
  have hg' : AEStronglyMeasurable g (Measure.map (c • ·) volume) := by
    rw [hmap]; exact hg.smul_measure _
  rw [show (fun ξ => g (c • ξ)) = g ∘ (c • ·) from rfl,
    ← eLpNorm_map_measure hg' (measurable_const_smul c).aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_zero]
  · simp [finrank_euclideanSpace, abs_of_pos hc]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity

theorem norm_scaleOp (h1 : FieldOpRealized) {c : ℝ} (hc : 0 < c) (f : L2C) :
    ‖scaleOp c f‖ = c * ((c ^ 3)⁻¹) ^ (1 / 2 : ℝ) * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (scaleOp_realized h1 hc.ne' f),
    show (fun ξ => c • (f : Space → CSpace) (c • ξ)) = c • (fun ξ => (f : Space → CSpace) (c • ξ))
      from rfl, eLpNorm_const_smul, eLpNorm_comp_smul hc _ (Lp.aestronglyMeasurable f),
    ENNReal.toReal_mul, ENNReal.toReal_mul, Lp.norm_def, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity)]
  simp [abs_of_pos hc, mul_assoc]

theorem tendsto_scaleOp_of_compact (h1 : FieldOpRealized) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {g : Space → CSpace} (hgc : Continuous g) (hgs : HasCompactSupport g) {G : L2C}
    (hG : (G : Space → CSpace) =ᵐ[volume] g) :
    Tendsto (fun c => scaleOp c G) (𝓝 c₀) (𝓝 (scaleOp c₀ G)) := by
  have hreal : ∀ c : ℝ, c ≠ 0 → (scaleOp c G : Space → CSpace) =ᵐ[volume] fun ξ => c • g (c • ξ) := by
    intro c hc
    refine (scaleOp_realized h1 hc G).trans ?_
    have := (Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc).ae_eq_comp hG
    filter_upwards [this] with ξ hξ
    simp only [Function.comp_apply] at hξ
    rw [hξ]
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  obtain ⟨R₀, hR₀⟩ := hgs.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : ∀ y : Space, R < ‖y‖ → g y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport (fun hm => ?_)
    have := closedBall_subset_closedBall (le_max_left R₀ 1) (hR₀ hm)
    rw [mem_closedBall, dist_zero_right] at this
    exact absurd hy (not_lt.2 this)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set H : ℝ → Space → CSpace := fun c ξ => c • g (c • ξ) - c₀ • g (c₀ • ξ)
  set K : Set Space := closedBall 0 (2 * R / c₀)
  set B : ℝ≥0∞ := ENNReal.ofReal (3 * c₀ * C) ^ (2 : ℝ)
  have hHc : ∀ c, Continuous (H c) := fun c =>
    ((hgc.comp (continuous_const_smul c)).const_smul c).sub
      ((hgc.comp (continuous_const_smul c₀)).const_smul c₀)
  have hL : Tendsto (fun c => ∫⁻ ξ, ‖H c ξ‖ₑ ^ (2 : ℝ)) (𝓝 c₀) (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 c₀)
      (F := fun c ξ => ‖H c ξ‖ₑ ^ (2 : ℝ)) (f := fun _ => 0) (K.indicator fun _ => B)
      (Eventually.of_forall fun c => ((hHc c).measurable.enorm.pow_const _))
      ?_ ?_ ?_
    · simpa using this
    · filter_upwards [Ioo_mem_nhds (half_lt_self hc₀) (lt_two_mul_self hc₀)] with c hc
      refine Eventually.of_forall fun ξ => ?_
      by_cases hξ : ξ ∈ K
      · rw [indicator_of_mem hξ]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖H c ξ‖ ≤ ‖c • g (c • ξ)‖ + ‖c₀ • g (c₀ • ξ)‖ := norm_sub_le _ _
          _ ≤ c * C + c₀ * C := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (show 0 ≤ c by linarith [hc.1]),
              Real.norm_of_nonneg hc₀.le]
            gcongr
            · linarith [hc.1]
            · exact hC _
            · exact hC _
          _ ≤ 3 * c₀ * C := by nlinarith [hc.2]
      · have hn : 2 * R / c₀ < ‖ξ‖ := by
          simpa [K, mem_closedBall, dist_zero_right, not_le] using hξ
        have hRξ : 2 * R < c₀ * ‖ξ‖ := by rwa [div_lt_iff₀' hc₀] at hn
        have h1' : g (c • ξ) = 0 := hsupp _ (by
          rw [norm_smul, Real.norm_of_nonneg (by linarith [hc.1])]
          nlinarith [hc.1, norm_nonneg ξ])
        have h2' : g (c₀ • ξ) = 0 := hsupp _ (by
          rw [norm_smul, Real.norm_of_nonneg hc₀.le]
          linarith)
        simp [H, h1', h2']
    · rw [lintegral_indicator_const measurableSet_closedBall]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun ξ => ?_
      have hcont : Continuous fun c : ℝ => H c ξ :=
        (continuous_id.smul (hgc.comp (continuous_id.smul continuous_const))).sub continuous_const
      have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp (hcont.tendsto c₀))
      simpa [H, Function.comp_def] using this
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hev : (fun c => eLpNorm (⇑(scaleOp c G) - ⇑(scaleOp c₀ G)) 2 volume) =ᶠ[𝓝 c₀]
      fun c => (∫⁻ ξ, ‖H c ξ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hc₀] with c hc
    rw [eLpNorm_congr_ae ((hreal c (ne_of_gt hc)).sub (hreal c₀ hc₀.ne')),
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp [H]
  rw [tendsto_congr' hev]
  have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto _).comp hL
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using this

theorem tendsto_scaleOp (h1 : FieldOpRealized) {c₀ : ℝ} (hc₀ : 0 < c₀) (f : L2C) :
    Tendsto (fun c => scaleOp c f) (𝓝 c₀) (𝓝 (scaleOp c₀ f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set k : ℝ → ℝ := fun c => c * ((c ^ 3)⁻¹) ^ (1 / 2 : ℝ)
  have hk : ContinuousAt k c₀ :=
    continuousAt_id.mul (((continuousAt_id.pow 3).inv₀ (pow_ne_zero 3 hc₀.ne')).rpow_const
      (Or.inr (by norm_num)))
  have hk0 : 0 ≤ k c₀ := by positivity
  set K := k c₀ + 1
  have hK : 0 < K := by positivity
  obtain ⟨G, ⟨g, hGg, hgs, hgd⟩, hfG⟩ :=
    (Lp.dense_hasCompactSupport_contDiff (E := Space) (F := CSpace) (μ := volume) (p := 2)
      ENNReal.ofNat_ne_top).exists_dist_lt f (show 0 < ε / (3 * K) by positivity)
  have hsm := tendsto_scaleOp_of_compact h1 hc₀ hgd.continuous hgs hGg
  have hbound : ∀ c, 0 < c → k c ≤ K → dist (scaleOp c f) (scaleOp c G) < ε / 3 := by
    intro c hc hkc
    rw [dist_eq_norm, ← map_sub, norm_scaleOp h1 hc, ← dist_eq_norm]
    calc k c * dist f G ≤ K * dist f G := by gcongr
      _ < K * (ε / (3 * K)) := by gcongr
      _ = ε / 3 := by field_simp
  filter_upwards [hk.eventually_lt continuousAt_const (lt_add_one (k c₀)), Ioi_mem_nhds hc₀,
    Metric.tendsto_nhds.1 hsm (ε / 3) (by positivity)] with c hkc hc hcG
  calc dist (scaleOp c f) (scaleOp c₀ f)
      ≤ dist (scaleOp c f) (scaleOp c G) + dist (scaleOp c G) (scaleOp c₀ G) +
        dist (scaleOp c₀ G) (scaleOp c₀ f) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact hbound c hc hkc.le
      · rw [dist_comm]; exact hbound c₀ hc₀ (by linarith)
    _ = ε := by ring

end Internal.DilationCont

open Internal.DilationCont in
theorem dilationContinuous (h1 : FieldOpRealized) (h2 : DilationAlgebra) :
    DilationContinuous := by
  intro x
  refine continuousOn_of_forall_continuousAt fun μ₀ hμ₀ => ?_
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  have heq : (Subtype.val ∘ fun μ => dilX μ x) =ᶠ[𝓝 μ₀]
      fun μ => scaleOp (Real.sqrt μ)⁻¹ (x : L2C) := by
    filter_upwards [Ioi_mem_nhds hμ₀] with μ hμ
    exact h2.2.2.2.2 μ hμ x
  refine ContinuousAt.congr ?_ heq.symm
  have hs : ContinuousAt (fun μ : ℝ => (Real.sqrt μ)⁻¹) μ₀ :=
    Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.2 hμ₀).ne'
  exact (tendsto_scaleOp h1 (inv_pos.2 (Real.sqrt_pos.2 hμ₀)) _).comp hs

end Breakdown.Freq
