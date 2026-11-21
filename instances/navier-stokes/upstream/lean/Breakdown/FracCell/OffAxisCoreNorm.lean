import Breakdown.FracCell.OffAxisCoreSt

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.OffAxisCoreNorm

open Internal.SpectralBlocksMode

theorem cont_slice {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) (r : ℝ) :
    Continuous fun z => F r z :=
  hF.comp (continuous_const.prodMk continuous_id)

theorem cont_inner {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) (c d : ℝ) :
    Continuous fun r => ∫ z in c..d, F r z :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := F) hF c d

theorem rect_sum {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ → ℝ)
    (hF : ∀ i, Continuous fun p : ℝ × ℝ => F i p.1 p.2) (a b c d : ℝ) :
    (∫ r in a..b, ∫ z in c..d, ∑ i ∈ S, F i r z) = ∑ i ∈ S, ∫ r in a..b, ∫ z in c..d, F i r z := by
  have e : ∀ r, (∫ z in c..d, ∑ i ∈ S, F i r z) = ∑ i ∈ S, ∫ z in c..d, F i r z := fun r =>
    intervalIntegral.integral_finsetSum fun i _ => (cont_slice (hF i) r).intervalIntegrable _ _
  simp only [e]
  exact intervalIntegral.integral_finsetSum fun i _ => (cont_inner (hF i) c d).intervalIntegrable _ _

theorem trig_cross (m : ℕ) : ∫ θ in (-π)..π, trigMode 0 ((m : ℝ) * θ) * trigMode 1 ((m : ℝ) * θ) = 0 := by
  have e : ∀ θ : ℝ, trigMode 0 ((m : ℝ) * -θ) * trigMode 1 ((m : ℝ) * -θ)
      = -(trigMode 0 ((m : ℝ) * θ) * trigMode 1 ((m : ℝ) * θ)) := by
    intro θ
    simp [trigMode, mul_neg, Real.cos_neg, Real.sin_neg]
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun θ => trigMode 0 ((m : ℝ) * θ) * trigMode 1 ((m : ℝ) * θ))
  simp only [e, neg_neg, intervalIntegral.integral_neg] at h
  linarith

theorem trig_sq_int (m : ℕ) (a0 a1 : ℝ) :
    ∫ θ in (-π)..π, (trigMode 0 ((m : ℝ) * θ) * a0 + trigMode 1 ((m : ℝ) * θ) * a1) ^ 2
      = trigWeight m 0 * a0 ^ 2 + trigWeight m 1 * a1 ^ 2 := by
  have c0 := trig_cont 0 (m : ℝ)
  have c1 := trig_cont 1 (m : ℝ)
  have e : (fun θ : ℝ => (trigMode 0 ((m : ℝ) * θ) * a0 + trigMode 1 ((m : ℝ) * θ) * a1) ^ 2)
      = fun θ => a0 ^ 2 * trigMode 0 ((m : ℝ) * θ) ^ 2 + a1 ^ 2 * trigMode 1 ((m : ℝ) * θ) ^ 2
        + 2 * a0 * a1 * (trigMode 0 ((m : ℝ) * θ) * trigMode 1 ((m : ℝ) * θ)) := by
    funext θ
    ring
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, trig_cross]
  · unfold trigWeight
    ring
  · exact (continuous_const.mul (c0.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.mul (c1.pow 2)).intervalIntegrable _ _
  · exact ((continuous_const.mul (c0.pow 2)).add (continuous_const.mul (c1.pow 2))).intervalIntegrable _ _
  · exact (continuous_const.mul (c0.mul c1)).intervalIntegrable _ _

theorem mem_iff (g : CellBlock) (s : Fin 2) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    cylPoint r 0 z ∈ cellSolid g s ↔
      (r, z) ∈ Set.Icc g.innerRadius g.outerRadius ×ˢ Set.Icc (solidLower g s) (solidUpper g s) := by
  simp only [cellSolid, Set.mem_ofPred_eq, radial_cyl hr, cyl2, Set.mem_prod, Set.mem_Icc]
  fin_cases s
  · simp [solidLower, solidUpper, and_assoc]
  · simp only [solidLower, solidUpper]
    simp
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, by linarith, by linarith⟩

open Classical in
theorem norm_cyl (g : CellBlock) (f : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (hZ0 : 0 ≤ g.lowerHeight)
    {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) {z : ℝ} (hz : z ≠ 0) :
    ‖shapeField g f (cylPoint r θ z)‖ ^ 2 = ∑ s : Fin 2,
      (if cylPoint r 0 z ∈ cellSolid g s then (1 : ℝ) else 0) * ∑ c : Fin 3,
        (trigMode 0 (g.mode * θ) * f s c 0 r z + trigMode 1 (g.mode * θ) * f s c 1 r z) ^ 2 := by
  classical
  have hex : ¬ (cylPoint r 0 z ∈ cellSolid g 0 ∧ cylPoint r 0 z ∈ cellSolid g 1) := by
    rintro ⟨h0, h1⟩
    rw [mem_iff g 0 hr z] at h0
    rw [mem_iff g 1 hr z] at h1
    simp only [Set.mem_prod, Set.mem_Icc, solidLower, solidUpper] at h0 h1
    simp at h0 h1
    exact hz (by linarith [h0.2.1, h1.2.2])
  rw [← real_inner_self_eq_norm_sq, shape_cyl g f hr hθ z]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, frame_inner]
  by_cases h0 : cylPoint r 0 z ∈ cellSolid g 0 <;> by_cases h1 : cylPoint r 0 z ∈ cellSolid g 1
  · exact absurd ⟨h0, h1⟩ hex
  all_goals (simp [h0, h1, Fin.sum_univ_two, Fin.sum_univ_three]; try ring)

open Classical in
theorem theta_int (g : CellBlock) (f : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (hZ0 : 0 ≤ g.lowerHeight)
    {r : ℝ} (hr : 0 < r) {z : ℝ} (hz : z ≠ 0) :
    ∫ θ in (-π)..π, ‖shapeField g f (cylPoint r θ z)‖ ^ 2 = ∑ s : Fin 2,
      (if cylPoint r 0 z ∈ cellSolid g s then (1 : ℝ) else 0) * ∑ c : Fin 3,
        (trigWeight g.mode 0 * f s c 0 r z ^ 2 + trigWeight g.mode 1 * f s c 1 r z ^ 2) := by
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  have hc : ∀ s c, Continuous fun θ : ℝ =>
      (trigMode 0 (g.mode * θ) * f s c 0 r z + trigMode 1 (g.mode * θ) * f s c 1 r z) ^ 2 := fun s c =>
    (((trig_cont 0 _).mul continuous_const).add ((trig_cont 1 _).mul continuous_const)).pow 2
  rw [intervalIntegral.integral_of_le hpi,
    setIntegral_congr_fun measurableSet_Ioc (fun θ hθ => norm_cyl g f hZ0 hr hθ hz),
    ← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    · congr 1
      exact Finset.sum_congr rfl fun c _ => trig_sq_int g.mode _ _
    · intro c _
      exact (hc s c).intervalIntegrable _ _
  · intro s _
    exact (continuous_const.mul (continuous_finsetSum _ fun c _ => hc s c)).intervalIntegrable _ _

theorem shape_meas (g : CellBlock) (f : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ)
    (hf : ∀ s c t, Continuous (Function.uncurry (f s c t))) : Measurable (shapeField g f) := by
  unfold shapeField
  refine Finset.measurable_sum _ fun s _ => Measurable.indicator ?_ (Internal.SpectralBlocks.solid_meas g s)
  refine Finset.measurable_sum _ fun c _ => ?_
  refine Measurable.smul (f := fun w => ∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
    * f s c t (radialCoord w) (w 2)) (g := frameVector c) ?_ (Internal.SpectralBlocks.frame_meas c)
  refine Finset.measurable_sum _ fun t _ => Measurable.mul (Internal.SpectralBlocks.trig_meas t _) ?_
  exact (hf s c t).measurable.comp (Internal.SpectralBlocks.radial_cont.measurable.prodMk
    (Internal.SpectralBlocks.coord_cont 2).measurable)

theorem frame_norm (c : Fin 3) (y : Space) : ‖frameVector c y‖ ≤ 1 := by
  have h := frame_inner c c (angleCoord y)
  rw [if_pos rfl, real_inner_self_eq_norm_sq, ← frame_eq] at h
  nlinarith [norm_nonneg (frameVector c y)]

theorem trig_le (t : Fin 2) (x : ℝ) : ‖trigMode t x‖ ≤ 1 := by
  unfold trigMode
  split_ifs
  · exact (Real.norm_eq_abs _).trans_le (Real.abs_cos_le_one x)
  · exact (Real.norm_eq_abs _).trans_le (Real.abs_sin_le_one x)

theorem solid_bounds (g : CellBlock) (hZ0 : 0 ≤ g.lowerHeight) (hZ : g.lowerHeight < g.upperHeight)
    (s : Fin 2) {y : Space} (hy : y ∈ cellSolid g s) :
    g.innerRadius ≤ radialCoord y ∧ radialCoord y ≤ g.outerRadius ∧ -g.upperHeight ≤ y 2 ∧ y 2 ≤ g.upperHeight := by
  simp only [cellSolid, Set.mem_ofPred_eq] at hy
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine ⟨h1, h2, ?_, ?_⟩ <;> split_ifs at h3 h4 <;> linarith

theorem shapeNorm_core : ShapeNormStatement := by
  intro g f hRin hR hZ hZ0 hf
  classical
  set K : Set (ℝ × ℝ) := Set.Icc g.innerRadius g.outerRadius ×ˢ Set.Icc (-g.upperHeight) g.upperHeight
    with hK_def
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hb : ∀ s c t, ∃ M, 0 ≤ M ∧ ∀ q ∈ K, ‖f s c t q.1 q.2‖ ≤ M := by
    intro s c t
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hf s c t).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun q hq => (hM q hq).trans (le_max_left _ _)⟩
  choose Mb hM0 hMb using hb
  have hbound : ∀ y, ‖shapeField g f y‖ ≤ ∑ s : Fin 2, ∑ c : Fin 3, ∑ t : Fin 2, Mb s c t := by
    intro y
    unfold shapeField
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [Set.indicator_apply]
    split_ifs with hy
    · obtain ⟨h1, h2, h3, h4⟩ := solid_bounds g hZ0 hZ s hy
      have hq : (radialCoord y, y 2) ∈ K := ⟨⟨h1, h2⟩, h3, h4⟩
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      rw [norm_smul]
      refine (mul_le_of_le_one_right (norm_nonneg _) (frame_norm c y)).trans ?_
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (trig_le t _)).trans (hMb s c t _ hq)
    · rw [norm_zero]
      exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun t _ => hM0 s c t
  have hmeas := shape_meas g f hf
  set B : Set Space := ⋃ s, cellSolid g s with hB_def
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun s => Internal.SpectralBlocks.solid_meas g s
  have hBsub : B ⊆ Metric.closedBall 0 (g.outerRadius + g.upperHeight) := by
    intro y hy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hy
    obtain ⟨h1, h2, h3, h4⟩ := solid_bounds g hZ0 hZ s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have hn : ‖y‖ ^ 2 = radialCoord y ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, radialCoord, Real.sq_sqrt (by positivity)]
      simp only [Real.norm_eq_abs, sq_abs]
    have hr0 : 0 ≤ radialCoord y := Real.sqrt_nonneg _
    nlinarith [norm_nonneg y]
  have hBfin : volume B < ⊤ := (measure_mono hBsub).trans_lt measure_closedBall_lt_top
  have hind : shapeField g f = B.indicator (shapeField g f) := by
    funext y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
    · have hs : ∀ s, y ∉ cellSolid g s := fun s h => hy (Set.mem_iUnion.2 ⟨s, h⟩)
      rw [Set.indicator_apply, if_neg hy]
      unfold shapeField
      exact Finset.sum_eq_zero fun s _ => by rw [Set.indicator_apply, if_neg (hs s)]
  have hmem : MemLp (shapeField g f) 2 volume := by
    rw [hind, memLp_indicator_iff_restrict hBm]
    have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin.ne
    exact MemLp.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbound)
  refine ⟨hmem, ?_⟩
  have hint : Integrable (fun y => ‖shapeField g f y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem.1).1 hmem
  rw [cylIntegral _ hint]
  set R : Fin 2 → Set (ℝ × ℝ) := fun s =>
    Set.Icc g.innerRadius g.outerRadius ×ˢ Set.Icc (solidLower g s) (solidUpper g s) with hR_def
  set H : Fin 2 → ℝ × ℝ → ℝ := fun s q => q.1 * ∑ c : Fin 3,
    (trigWeight g.mode 0 * f s c 0 q.1 q.2 ^ 2 + trigWeight g.mode 1 * f s c 1 q.1 q.2 ^ 2) with hH_def
  have hfc : ∀ s c t, Continuous fun q : ℝ × ℝ => f s c t q.1 q.2 := fun s c t => hf s c t
  have hcH : ∀ s, Continuous (H s) := fun s =>
    continuous_fst.mul (continuous_finsetSum _ fun c _ =>
      (continuous_const.mul ((hfc s c 0).pow 2)).add (continuous_const.mul ((hfc s c 1).pow 2)))
  have hRm : ∀ s, MeasurableSet (R s) := fun s => measurableSet_Icc.prod measurableSet_Icc
  have hSm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hnull : ∀ᵐ q : ℝ × ℝ ∂volume, q.2 ≠ 0 := by
    have e : {q : ℝ × ℝ | q.2 = 0} = Set.univ ×ˢ {0} := by
      ext q
      simp
    refine ae_iff.2 ?_
    simp only [ne_eq, not_not]
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hae : ∀ᵐ q ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))),
      q.1 * ∫ θ in (-π)..π, ‖shapeField g f (cylPoint q.1 θ q.2)‖ ^ 2 = ∑ s : Fin 2, (R s).indicator (H s) q := by
    rw [ae_restrict_iff' hSm]
    filter_upwards [hnull] with q hq hqS
    have hq1 : 0 < q.1 := hqS.1
    rw [theta_int g f hZ0 hq1 hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Set.indicator_apply]
    by_cases hm : cylPoint q.1 0 q.2 ∈ cellSolid g s
    · have hmR : q ∈ R s := (mem_iff g s hq1 q.2).1 hm
      rw [if_pos hm, if_pos hmR, one_mul]
    · have hmR : q ∉ R s := fun h => hm ((mem_iff g s hq1 q.2).2 h)
      rw [if_neg hm, if_neg hmR, zero_mul, mul_zero]
  have hRS : ∀ s, Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) ∩ R s = R s := fun s =>
    Set.inter_eq_right.2 fun q hq => ⟨lt_of_lt_of_le hRin hq.1.1, Set.mem_univ _⟩
  have hHi : ∀ s, IntegrableOn (H s) (R s) := fun s =>
    (hcH s).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [integral_congr_ae hae, integral_finsetSum]
  swap
  · intro s _
    exact ((hHi s).integrable_indicator (hRm s)).integrableOn
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [setIntegral_indicator (hRm s), hRS s]
  have hHi' : IntegrableOn (H s) (Set.Icc g.innerRadius g.outerRadius ×ˢ Set.Icc (solidLower g s) (solidUpper g s))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hHi s
  show ∫ x in Set.Icc g.innerRadius g.outerRadius ×ˢ Set.Icc (solidLower g s) (solidUpper g s), H s x = _
  rw [Measure.volume_eq_prod, setIntegral_prod _ hHi']
  have hpR : g.innerRadius ≤ g.outerRadius := hR.le
  have hpZ : solidLower g s ≤ solidUpper g s := by
    fin_cases s
    · simp [solidLower, solidUpper]
      linarith
    · simp only [solidLower, solidUpper]
      simp
      linarith
  have hin : ∀ r, (∫ z in Set.Icc (solidLower g s) (solidUpper g s), H s (r, z))
      = ∫ z in solidLower g s..solidUpper g s, H s (r, z) := fun r => by
    rw [intervalIntegral.integral_of_le hpZ, integral_Icc_eq_integral_Ioc]
  simp only [hin]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpR]
  have e : ∀ r z, H s (r, z) = ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t * (f s c t r z ^ 2 * r) := by
    intro r z
    simp only [hH_def, Fin.sum_univ_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp only [e]
  rw [rect_sum _ _ (fun c => continuous_finsetSum _ fun t _ =>
    continuous_const.mul (((hfc s c t).pow 2).mul continuous_fst))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [rect_sum _ _ (fun t => continuous_const.mul (((hfc s c t).pow 2).mul continuous_fst))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [intervalIntegral.integral_const_mul]

end Internal.OffAxisCoreNorm

theorem shapeNorm_holds : ShapeNormStatement :=
  Internal.OffAxisCoreNorm.shapeNorm_core

end Spectral

end CellCert

end Breakdown
