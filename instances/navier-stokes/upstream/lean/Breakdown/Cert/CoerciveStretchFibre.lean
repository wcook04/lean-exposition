import Breakdown.Cert.CoerciveModeRotation

open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace StretchFibreInternal

open Internal.ModeRotation

theorem quasiMeasurePreserving_fibreMap (hRot : AxialRotationHolds) :
    Measure.QuasiMeasurePreserving (fun w : (ℝ × ℝ) × Space => ((w.1.1, axialRot w.1.2 w.2) : ℝ × Space))
      (boxMeasure.prod volume) volume := by
  have hpair : Continuous (fun w : (ℝ × ℝ) × Space => ((w.1.2, w.2) : ℝ × Space)) := by fun_prop
  have hc : Continuous (fun w : (ℝ × ℝ) × Space => axialRot w.1.2 w.2) := by
    have h := continuous_axialRot.comp hpair
    exact h
  have hm : Measurable (fun w : (ℝ × ℝ) × Space => ((w.1.1, axialRot w.1.2 w.2) : ℝ × Space)) :=
    (continuous_fst.fst.prodMk hc).measurable
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun N hN h0 => ?_⟩
  rw [Measure.map_apply hm hN, Measure.prod_apply (hm hN)]
  rw [Measure.volume_eq_prod] at h0
  have hslice := (Measure.measure_prod_null hN).1 h0
  have hrot : ∀ p : ℝ × ℝ, (volume : Measure Space)
      (Prod.mk p ⁻¹' ((fun w : (ℝ × ℝ) × Space => ((w.1.1, axialRot w.1.2 w.2) : ℝ × Space)) ⁻¹' N))
        = (volume : Measure Space) (Prod.mk p.1 ⁻¹' N) := by
    intro p
    obtain ⟨R, hR⟩ := hRot.1 p.2
    have e : Prod.mk p ⁻¹' ((fun w : (ℝ × ℝ) × Space => ((w.1.1, axialRot w.1.2 w.2) : ℝ × Space)) ⁻¹' N)
        = R ⁻¹' (Prod.mk p.1 ⁻¹' N) := by
      ext y
      simp [hR]
    rw [e, R.measurePreserving.measure_preimage (measurable_prodMk_left hN).nullMeasurableSet]
  simp_rw [hrot]
  have hae : ∀ᵐ p ∂boxMeasure, (volume : Measure Space) (Prod.mk p.1 ⁻¹' N) = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae hslice)
  rw [lintegral_congr_ae hae, lintegral_zero]

theorem ae_memLp_fibre (hRot : AxialRotationHolds) {E : Type*} [NormedAddCommGroup E]
    {u : ℝ → Space → E} (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) volume)
    (hfin : ∀ R : ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖u σ y‖ ^ 2) < ⊤) :
    ∀ᵐ y : Space, MemLp (fun p : ℝ × ℝ => u p.1 (axialRot p.2 y)) 2 boxMeasure := by
  have hF : AEStronglyMeasurable (fun w : (ℝ × ℝ) × Space => u w.1.1 (axialRot w.1.2 w.2))
      (boxMeasure.prod volume) :=
    hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_fibreMap hRot)
  have hswap : AEStronglyMeasurable (fun w : Space × (ℝ × ℝ) => u w.2.1 (axialRot w.2.2 w.1))
      ((volume : Measure Space).prod boxMeasure) := hF.prod_swap
  have hmeas : ∀ᵐ y : Space, AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1 (axialRot p.2 y)) boxMeasure :=
    hswap.prodMk_left
  have hfinN : ∀ N : ℕ, ∀ᵐ y : Space, y ∈ Metric.closedBall (0 : Space) N →
      ∫⁻ p, ENNReal.ofReal (‖u p.1 (axialRot p.2 y)‖ ^ 2) ∂boxMeasure < ⊤ := by
    intro N
    rw [← ae_restrict_iff' Metric.isClosed_closedBall.measurableSet]
    have hJ : AEMeasurable (fun w : Space × (ℝ × ℝ) => ENNReal.ofReal (‖u w.2.1 (axialRot w.2.2 w.1)‖ ^ 2))
        ((volume.restrict (Metric.closedBall (0 : Space) N)).prod boxMeasure) := by
      have e : (volume.restrict (Metric.closedBall (0 : Space) N)).prod boxMeasure =
          ((volume : Measure Space).prod boxMeasure).restrict (Metric.closedBall (0 : Space) N ×ˢ Set.univ) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [e]
      exact (ENNReal.measurable_ofReal.comp_aemeasurable (hswap.norm.aemeasurable.pow_const 2)).restrict
    refine ae_lt_top' hJ.lintegral_prod_right' ?_
    rw [lintegral_lintegral_swap hJ]
    have hinner : ∀ p : ℝ × ℝ, ∫⁻ y in Metric.closedBall (0 : Space) N,
        ENNReal.ofReal (‖u p.1 (axialRot p.2 y)‖ ^ 2) =
          ∫⁻ y in Metric.closedBall (0 : Space) N, ENNReal.ofReal (‖u p.1 y‖ ^ 2) := by
      intro p
      obtain ⟨R, hR⟩ := hRot.1 p.2
      rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        ← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
      conv_rhs => rw [← R.measurePreserving.lintegral_comp_emb R.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
      refine lintegral_congr fun y => ?_
      have hyB : R y ∈ Metric.closedBall (0 : Space) N ↔ y ∈ Metric.closedBall (0 : Space) N := by
        rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, hR, norm_axialRot hRot]
      by_cases hy : y ∈ Metric.closedBall (0 : Space) N
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hyB.2 hy), hR]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hyB.1 h))]
    simp_rw [hinner]
    have hK : AEMeasurable (fun t : ℝ => ∫⁻ y in Metric.closedBall (0 : Space) N,
        ENNReal.ofReal (‖u t y‖ ^ 2)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      have hu2 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖u z.1 z.2‖ ^ 2))
          ((volume : Measure ℝ).prod (volume.restrict (Metric.closedBall (0 : Space) N))) := by
        have e : (volume : Measure ℝ).prod (volume.restrict (Metric.closedBall (0 : Space) N)) =
            ((volume : Measure ℝ).prod (volume : Measure Space)).restrict
              (Set.univ ×ˢ Metric.closedBall (0 : Space) N) := by
          rw [← Measure.prod_restrict, Measure.restrict_univ]
        rw [e, ← Measure.volume_eq_prod]
        exact (ENNReal.measurable_ofReal.comp_aemeasurable (hu.norm.aemeasurable.pow_const 2)).restrict
      exact hu2.lintegral_prod_right'.mono_measure Measure.restrict_le_self
    rw [show boxMeasure = (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) from rfl]
    have hK2 : AEMeasurable (fun z : ℝ × ℝ => ∫⁻ y in Metric.closedBall (0 : Space) N,
        ENNReal.ofReal (‖u z.1 y‖ ^ 2))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) :=
      hK.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    rw [lintegral_prod _ hK2]
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_ne_top (ne_of_lt ?_) ENNReal.ofReal_ne_top
    exact lt_of_le_of_lt (lintegral_mono_set Set.Ioc_subset_Icc_self) (hfin N)
  have hall := ae_all_iff.2 hfinN
  filter_upwards [hall, hmeas] with y h1 h2
  obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
  have hlt := h1 N (mem_closedBall_zero_iff.2 hN)
  rw [memLp_two_iff_integrable_sq_norm h2]
  refine ⟨h2.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => by positivity)]
  exact hlt

theorem ae_memLp_fibre_vel (hRot : AxialRotationHolds) (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ y : Space, MemLp (fun p : ℝ × ℝ => v p.1 (axialRot p.2 y)) 2 boxMeasure := by
  have hfin := hLoc Γ P v G H g hv
  exact ae_memLp_fibre (E := Space) (u := v) hRot hv.measurable_velocity hfin

theorem ae_memLp_fibre_grad (hRot : AxialRotationHolds)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (k : Fin 3) :
    ∀ᵐ y : Space, MemLp (fun p : ℝ × ℝ => G p.1 (axialRot p.2 y) (unitVector k)) 2 boxMeasure := by
  have hc : Continuous (fun q : Space →L[ℝ] Space => q (unitVector k)) := by fun_prop
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector k)) volume := by
    have h := hc.comp_aestronglyMeasurable hv.measurable_gradient
    exact h
  refine ae_memLp_fibre (E := Space) (u := fun σ y => G σ y (unitVector k)) hRot hm (fun R => ?_)
  have hg := hv.gradient_finite
  unfold periodLIntegral at hg
  refine lt_of_le_of_lt ?_ hg
  refine lintegral_mono fun σ => ?_
  refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  unfold matSq
  exact Finset.single_le_sum (f := fun i => ‖G σ y (unitVector i)‖ ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ k)

end StretchFibreInternal

end Coercive

end Breakdown
