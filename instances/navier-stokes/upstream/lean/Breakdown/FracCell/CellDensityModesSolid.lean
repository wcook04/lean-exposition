import Breakdown.FracCell.StCellBound
import Breakdown.FracCell.CylIntegral
import Breakdown.FracCert.LinearSolveCore

open MeasureTheory Real Set

noncomputable section

namespace Breakdown.FracInternal.CellDensityModesSolid

open SteadyCert CellCert CellCert.CellAnalysis

theorem cyl_radius {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  simp only [cylRadius, cylPoint]
  simp
  rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ]
  exact Real.sqrt_sq hr

theorem cyl_height (r θ z : ℝ) : cylHeight (cylPoint r θ z) = z := by
  simp [cylHeight, cylPoint]

theorem cyl_periodic (r z : ℝ) (f : Space → ℝ) :
    Function.Periodic (fun θ => f (cylPoint r θ z)) (2 * π) := by
  intro θ
  simp only [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem plane_null : volume {y : Space | y 2 = 0} = 0 := by
  have h : {y : Space | y 2 = 0} = (LinearMap.ker (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap : Set Space) := by
    ext y; simp
  rw [h]
  refine Measure.addHaar_submodule _ _ ?_
  intro htop
  have : EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∈ LinearMap.ker (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap := by
    rw [htop]; trivial
  simp at this


theorem solid_closed (K : CellBox) : MeasurableSet K.solid := by
  have hR : Continuous cylRadius := by unfold cylRadius; fun_prop
  have hH : Continuous cylHeight := by unfold cylHeight; fun_prop
  have : IsClosed K.solid := by
    simp only [CellBox.solid, Set.ofPred_and]
    exact (isClosed_le continuous_const hR).inter ((isClosed_le hR continuous_const).inter
      ((isClosed_le continuous_const hH.abs).inter (isClosed_le hH.abs continuous_const)))
  exact this.measurableSet

theorem mirror_two (y : Space) : mirror y 2 = -(y 2) := by simp [mirror]

theorem mirror_radius (y : Space) : cylRadius (mirror y) = cylRadius y := by simp [cylRadius, mirror]

theorem mirror_height (y : Space) : |cylHeight (mirror y)| = |cylHeight y| := by
  simp [cylHeight, mirror, abs_neg]

theorem mirror_pre (K : CellBox) :
    mirror ⁻¹' (K.solid ∩ {y : Space | 0 < y 2}) = K.solid \ {y : Space | 0 ≤ y 2} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq, CellBox.solid,
    mirror_radius, mirror_height, mirror_two, not_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

theorem pos_ae (K : CellBox) :
    (K.solid ∩ {y : Space | 0 < y 2} : Set Space) =ᵐ[volume] (K.solid ∩ {y : Space | 0 ≤ y 2} : Set Space) := by
  refine (ae_eq_set).2 ⟨?_, ?_⟩
  · have : (K.solid ∩ {y : Space | 0 < y 2}) \ (K.solid ∩ {y : Space | 0 ≤ y 2}) = ∅ := by
      ext y; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨⟨_, h⟩, h'⟩; exact h' ⟨‹_›, h.le⟩
    rw [this, measure_empty]
  · refine measure_mono_null (fun y hy => ?_) plane_null
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and, not_lt] at hy ⊢
    exact le_antisymm (hy.2 hy.1.1) hy.1.2

theorem half_split (K : CellBox) (f : Space → ℝ) (hf : IntegrableOn f K.solid)
    (hm : ∀ᵐ y ∂volume, y ∈ K.solid → f (mirror y) = f y) :
    (∫ y in K.solid, f y) = 2 * ∫ y in K.solid ∩ {y : Space | 0 ≤ y 2}, f y := by
  have hP : MeasurableSet {y : Space | 0 ≤ y 2} :=
    measurableSet_le measurable_const ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable)
  have hP' : MeasurableSet {y : Space | 0 < y 2} :=
    measurableSet_lt measurable_const ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable)
  rw [← integral_inter_add_sdiff hP hf, ← mirror_pre]
  have hemb : MeasurableEmbedding mirror := by
    have hc : (⇑LinearSolveCore.mirrorIsometry : Space → Space) = mirror := rfl
    rw [← hc]
    exact LinearSolveCore.mirrorIsometry.toHomeomorph.measurableEmbedding
  have h1 : (∫ y in mirror ⁻¹' (K.solid ∩ {y : Space | 0 < y 2}), f y)
      = ∫ y in mirror ⁻¹' (K.solid ∩ {y : Space | 0 < y 2}), f (mirror y) := by
    have hms : MeasurableSet (mirror ⁻¹' (K.solid ∩ {y : Space | 0 < y 2})) := by
      rw [mirror_pre]; exact (solid_closed K).diff hP
    refine integral_congr_ae ((ae_restrict_iff' hms).2 (hm.mono fun y hy hyS => ?_))
    rw [mirror_pre] at hyS
    exact (hy hyS.1).symm
  rw [h1, LinearSolveCore.mirror_measurePreserving.setIntegral_preimage_emb hemb,
    setIntegral_congr_set (pos_ae K)]
  ring


theorem cyl_mem {K : CellBox} (hK : IsCellBox K) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    cylPoint r θ z ∈ K.solid ∩ {y : Space | 0 ≤ y 2} ↔ (r, z) ∈ K.rect := by
  have h2 : cylPoint r θ z 2 = z := by simp [cylPoint]
  simp only [Set.mem_inter_iff, CellBox.solid, Set.mem_ofPred_eq, cyl_radius hr.le, cyl_height, h2,
    CellBox.rect, Set.mem_prod, Set.mem_Icc]
  have hz := hK.z_order.1
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    rw [abs_of_nonneg h5] at h3 h4
    exact ⟨⟨h1, h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have h5 : 0 ≤ z := le_trans hz h3
    rw [abs_of_nonneg h5]
    exact ⟨⟨h1, h2, h3, h4⟩, h5⟩

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem period_shift (r z : ℝ) (f : Space → ℝ) :
    (∫ θ in (-π)..π, f (cylPoint r θ z)) = ∫ θ in (0 : ℝ)..(2 * π), f (cylPoint r θ z) := by
  have := (cyl_periodic r z f).intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  exact this

theorem rect_ae {K : CellBox} (hK : IsCellBox K) :
    ((Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) ∩ K.rect : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
  refine (ae_eq_set).2 ⟨?_, ?_⟩
  · rw [Set.sdiff_eq_empty.2 Set.inter_subset_right, measure_empty]
  · have hnull : volume (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
    refine measure_mono_null (fun q hq => ?_) hnull
    rcases hq with ⟨hq1, hq2⟩
    have h0 : ¬ (0 < q.1) := fun h => hq2 ⟨⟨h, Set.mem_univ _⟩, hq1⟩
    have h1 : 0 ≤ q.1 := le_trans hK.r_order.1 hq1.1.1
    exact ⟨le_antisymm (not_lt.1 h0) h1, Set.mem_univ _⟩

theorem upper_cyl (K : CellBox) (hK : IsCellBox K) (f : Space → ℝ) (hf : IntegrableOn f K.solid) :
    (∫ y in K.solid ∩ {y : Space | 0 ≤ y 2}, f y)
      = ∫ p in K.rect, p.1 * ∫ θ in (0 : ℝ)..(2 * π), f (cylPoint p.1 θ p.2) := by
  have hP : MeasurableSet {y : Space | 0 ≤ y 2} :=
    measurableSet_le measurable_const ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable)
  have hU : MeasurableSet (K.solid ∩ {y : Space | 0 ≤ y 2}) := (solid_closed K).inter hP
  rw [← integral_indicator hU,
    Spectral.cylIntegral _ ((integrable_indicator_iff hU).2 (hf.mono_set Set.inter_subset_left))]
  have hc : Spectral.cylPoint = cylPoint := rfl
  rw [hc]
  have key : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
      q.1 * (∫ θ in (-π)..π, (K.solid ∩ {y : Space | 0 ≤ y 2}).indicator f (cylPoint q.1 θ q.2))
        = K.rect.indicator (fun p => p.1 * ∫ θ in (0 : ℝ)..(2 * π), f (cylPoint p.1 θ p.2)) q := by
    rintro ⟨r, z⟩ ⟨hr, -⟩
    simp only [Set.mem_Ioi] at hr
    by_cases hq : (r, z) ∈ K.rect
    · rw [Set.indicator_of_mem hq]
      have : ∀ θ, (K.solid ∩ {y : Space | 0 ≤ y 2}).indicator f (cylPoint r θ z) = f (cylPoint r θ z) :=
        fun θ => Set.indicator_of_mem ((cyl_mem hK hr θ z).2 hq) f
      simp only [this, period_shift]
    · rw [Set.indicator_of_notMem hq]
      have : ∀ θ, (K.solid ∩ {y : Space | 0 ≤ y 2}).indicator f (cylPoint r θ z) = 0 :=
        fun θ => Set.indicator_of_notMem (fun h => hq ((cyl_mem hK hr θ z).1 h)) f
      simp [this]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) key,
    setIntegral_indicator (rect_meas K), setIntegral_congr_set (rect_ae hK)]

theorem solid_formula (K : CellBox) (hK : IsCellBox K) (f : Space → ℝ) (hf : IntegrableOn f K.solid)
    (hm : ∀ᵐ y ∂volume, y ∈ K.solid → f (mirror y) = f y) :
    (∫ y in K.solid, f y) = 2 * ∫ p in K.rect, p.1 * ∫ θ in (0 : ℝ)..(2 * π), f (cylPoint p.1 θ p.2) := by
  rw [half_split K f hf hm, upper_cyl K hK f hf]

end Breakdown.FracInternal.CellDensityModesSolid
