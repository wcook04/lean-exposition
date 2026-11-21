import Breakdown.CertCell.TailAngularPlane
import Breakdown.Cert.CoerciveStretchTorus

open scoped ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.MeanStretch

open TailBand Coercive.Internal.ModeRotation Coercive.RotationInternal

theorem quasiMeasurePreserving_orbitPair :
    Measure.QuasiMeasurePreserving
      (fun w : (ℝ × ℝ) × (ℝ × ℝ) => ((w.2.1, axialRot w.2.2 (planePoint w.1)) : ℝ × Space))
      ((volume.restrict halfPlane).prod (volume : Measure (ℝ × ℝ))) volume := by
  have h1 := quasiMeasurePreserving_orbitPlane
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) × ℝ)
      ((volume.restrict halfPlane).prod ((volume : Measure ℝ).prod volume))
      (((volume.restrict halfPlane).prod volume).prod volume) :=
    MeasurePreserving.symm _ (measurePreserving_prodAssoc _ _ _)
  exact h1.comp h2.quasiMeasurePreserving

theorem ae_orbit {P : ℝ × Space → Prop} (h : ∀ᵐ z, P z) :
    ∀ᵐ p ∂(volume.restrict halfPlane), ∀ᵐ θ : ℝ × ℝ, P (θ.1, axialRot θ.2 (planePoint p)) :=
  Measure.ae_ae_of_ae_prod (quasiMeasurePreserving_orbitPair.ae h)

theorem ae_aestronglyMeasurable_orbit {X : Type*} [NormedAddCommGroup X] {u : ℝ × Space → X}
    (hu : AEStronglyMeasurable u volume) :
    ∀ᵐ p ∂(volume.restrict halfPlane),
      AEStronglyMeasurable (fun θ : ℝ × ℝ => u (θ.1, axialRot θ.2 (planePoint p))) volume :=
  (hu.comp_quasiMeasurePreserving quasiMeasurePreserving_orbitPair).prodMk_left

theorem boxMeasure_eq_prod : boxMeasure = ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := rfl

theorem boxMeasure_ac : boxMeasure ≪ ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  rw [boxMeasure_eq_prod]
  exact Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem continuous_orbit (p : ℝ × ℝ) :
    Continuous (fun θ : ℝ × ℝ => ((θ.1, axialRot θ.2 (planePoint p)) : ℝ × Space)) := by
  have h := Internal.AngularPlane.continuous_orbitPlane
  have hg : Continuous (fun θ : ℝ × ℝ => ((p, θ.2) : (ℝ × ℝ) × ℝ)) := continuous_const.prodMk continuous_snd
  have h2 := h.comp hg
  exact continuous_fst.prodMk h2

theorem lintegral_window_le (g : ℝ → ℝ≥0∞) (hper : ∀ φ, g (φ + 2 * Real.pi) = g φ) :
    ∫⁻ φ in Set.Ioc (0 : ℝ) (2 * Real.pi), g φ
      ≤ (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, g φ) + ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, g φ := by
  have hpi := Real.pi_pos
  have hsub : Set.Ioc (0 : ℝ) (2 * Real.pi) ⊆ Set.Ioo (-Real.pi) Real.pi ∪ Set.Icc Real.pi (2 * Real.pi) := by
    rintro x ⟨h1, h2⟩
    by_cases hx : x < Real.pi
    · exact Or.inl ⟨by linarith, hx⟩
    · exact Or.inr ⟨le_of_not_gt hx, h2⟩
  have hshift : ∫⁻ φ in Set.Icc Real.pi (2 * Real.pi), g φ = ∫⁻ φ in Set.Icc (-Real.pi) 0, g φ := by
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc,
      ← lintegral_add_right_eq_self (fun x => (Set.Icc Real.pi (2 * Real.pi)).indicator g x) (2 * Real.pi)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Set.Icc (-Real.pi) 0
    · have hx' : x + 2 * Real.pi ∈ Set.Icc Real.pi (2 * Real.pi) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', hper]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      rintro ⟨h1, h2⟩
      exact hx ⟨by linarith, by linarith⟩
  have hlast : ∫⁻ φ in Set.Icc Real.pi (2 * Real.pi), g φ ≤ ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, g φ := by
    rw [hshift, setLIntegral_congr (Ioc_ae_eq_Icc (a := -Real.pi) (b := 0)).symm]
    exact lintegral_mono_set fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  calc ∫⁻ φ in Set.Ioc (0 : ℝ) (2 * Real.pi), g φ
      ≤ ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi ∪ Set.Icc Real.pi (2 * Real.pi), g φ := lintegral_mono_set hsub
    _ ≤ (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, g φ) + ∫⁻ φ in Set.Icc Real.pi (2 * Real.pi), g φ :=
        lintegral_union_le _ _ _
    _ ≤ _ := add_le_add le_rfl hlast

theorem measurable_orbitSlice (F : ℝ × Space → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun x : (ℝ × ℝ) × ℝ => ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (x.2, axialRot φ (planePoint x.1))) := by
  have horb := Internal.AngularPlane.continuous_orbitPlane
  have h1 : Measurable (fun w : ((ℝ × ℝ) × ℝ) × ℝ => ((w.1.1, w.2) : (ℝ × ℝ) × ℝ)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h3 := horb.measurable.comp h1
  have hg := (measurable_snd.comp measurable_fst).prodMk h3
  have hm := hF.comp hg
  have := hm.lintegral_prod_right' (ν := volume.restrict (Set.Ioo (-Real.pi) Real.pi))
  exact this

theorem lintegral_orbit_cylindrical (F : ℝ × Space → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal p.1 *
        ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p))
      = ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y, F (τ, y) := by
  have hK := measurable_orbitSlice F hF
  have hcyl : ∀ τ : ℝ, ∫⁻ y, F (τ, y) = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p)) := fun τ =>
    lintegral_eq_cylindrical (fun y => F (τ, y)) (hF.comp (measurable_const.prodMk measurable_id))
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
    (f := fun τ p => ENNReal.ofReal p.1 * ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p)))
    (((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul
      (hK.comp (measurable_snd.prodMk measurable_fst))).aemeasurable)
  simp_rw [hcyl]
  rw [hswap]
  refine lintegral_congr fun p => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem ae_lintegral_orbit_lt_top (F : ℝ × Space → ℝ≥0∞) (hF : Measurable F)
    (hfin : ∀ N : ℕ, ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) N, F (τ, y) < ⊤) :
    ∀ᵐ p ∂(volume.restrict halfPlane), ∫⁻ θ, F (θ.1, axialRot θ.2 (planePoint p)) ∂boxMeasure < ⊤ := by
  have step : ∀ N : ℕ, ∀ᵐ p ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))),
      ‖planePoint p‖ ≤ N →
        ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p)) < ⊤ := by
    intro N
    have hmS : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Space) N) :=
      MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet
    have hFN : Measurable (((Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Space) N).indicator F) :=
      hF.indicator hmS
    have hval : ∀ τ y, ((Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Space) N).indicator F (τ, y)
        = (Metric.closedBall (0 : Space) N).indicator (fun y => F (τ, y)) y := by
      intro τ y
      by_cases hy : y ∈ Metric.closedBall (0 : Space) N
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_prod.2 ⟨Set.mem_univ _, hy⟩)]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (Set.mem_prod.1 h).2)]
    have hI := lintegral_orbit_cylindrical _ hFN
    have hfinN : ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y, ((Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Space) N).indicator F (τ, y) < ⊤ := by
      refine lt_of_le_of_lt (le_of_eq ?_) (hfin N)
      refine lintegral_congr fun τ => ?_
      simp_rw [hval]
      rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    rw [← hI] at hfinN
    have hm2 := (ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((measurable_orbitSlice _ hFN).lintegral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) 1)))
    filter_upwards [ae_lt_top hm2 hfinN.ne, ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp hpS hpN
    have hp1 : (0 : ℝ) < p.1 := hpS.1
    have hlt : ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
        ((Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Space) N).indicator F (τ, axialRot φ (planePoint p)) < ⊤ := by
      rcases ENNReal.mul_lt_top_iff.1 hp with h | h | h
      · exact h.2
      · exact absurd h (by simp [hp1])
      · exact (le_of_eq h).trans_lt ENNReal.zero_lt_top
    refine lt_of_le_of_lt (le_of_eq ?_) hlt
    refine lintegral_congr fun τ => lintegral_congr fun φ => ?_
    rw [hval, Set.indicator_of_mem]
    rw [Metric.mem_closedBall, dist_zero_right, axialRot_norm]
    exact hpN
  have hall := ae_all_iff.2 step
  have hS : ∀ᵐ p ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))),
      ∫⁻ θ, F (θ.1, axialRot θ.2 (planePoint p)) ∂boxMeasure < ⊤ := by
    filter_upwards [hall] with p hp
    obtain ⟨N, hN⟩ := exists_nat_ge ‖planePoint p‖
    have h1 := hp N hN
    have hm0 := hF.comp (continuous_orbit p).measurable
    have hm : Measurable (fun θ : ℝ × ℝ => F (θ.1, axialRot θ.2 (planePoint p))) := hm0
    have hprod : ∫⁻ θ, F (θ.1, axialRot θ.2 (planePoint p)) ∂boxMeasure
        = ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ φ in Set.Ioc (0 : ℝ) (2 * Real.pi), F (τ, axialRot φ (planePoint p)) :=
      lintegral_prod _ hm.aemeasurable
    rw [hprod]
    have hwin : ∀ τ, ∫⁻ φ in Set.Ioc (0 : ℝ) (2 * Real.pi), F (τ, axialRot φ (planePoint p))
        ≤ (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p)))
          + ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p)) := by
      intro τ
      refine lintegral_window_le (fun φ => F (τ, axialRot φ (planePoint p))) fun φ => ?_
      rw [show φ + 2 * Real.pi = φ + ((1 : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring,
        Internal.AngularPlane.axialRot_add_int_mul]
    have hmφ0 := (measurable_orbitSlice F hF).comp ((measurable_const (a := p)).prodMk measurable_id)
    have hmφ : Measurable (fun τ : ℝ => ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p))) := hmφ0
    refine lt_of_le_of_lt (lintegral_mono hwin) ?_
    rw [lintegral_add_left hmφ]
    exact ENNReal.add_lt_top.2 ⟨h1, h1⟩
  exact ae_restrict_of_ae_restrict_of_subset (Set.prod_mono le_rfl (Set.subset_univ _)) hS


theorem ae_memLp_orbit {E : Type*} [NormedAddCommGroup E] {u : ℝ → Space → E}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) volume)
    (hfin : ∀ R : ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖u σ y‖ ^ 2) < ⊤) :
    ∀ᵐ p ∂(volume.restrict halfPlane),
      MemLp (fun θ : ℝ × ℝ => u θ.1 (axialRot θ.2 (planePoint p))) 2 boxMeasure := by
  obtain ⟨w, hw, heq⟩ : ∃ w : ℝ × Space → E, StronglyMeasurable w ∧ (fun z : ℝ × Space => u z.1 z.2) =ᵐ[volume] w :=
    ⟨hu.mk _, hu.stronglyMeasurable_mk, hu.ae_eq_mk⟩
  have hF : Measurable (fun z : ℝ × Space => ENNReal.ofReal (‖w z‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hw.norm.measurable.pow_const 2)
  have hG : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖u z.1 z.2‖ ^ 2)) volume :=
    (hu.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hvol : (volume : Measure (ℝ × Space)) = (volume : Measure ℝ).prod (volume : Measure Space) := rfl
  have hfinF : ∀ N : ℕ, ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) N,
      ENNReal.ofReal (‖w (τ, y)‖ ^ 2) < ⊤ := by
    intro N
    have hGr : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖u z.1 z.2‖ ^ 2))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Metric.closedBall (0 : Space) N))) := by
      rw [Measure.prod_restrict, ← hvol]
      exact hG.restrict
    have e1 : ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) N,
        ENNReal.ofReal (‖w (τ, y)‖ ^ 2)
        = ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) N, ENNReal.ofReal (‖w z‖ ^ 2) := by
      rw [hvol, ← Measure.prod_restrict, lintegral_prod _ hF.aemeasurable]
    have e2 : ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) N, ENNReal.ofReal (‖u τ y‖ ^ 2)
        = ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) N, ENNReal.ofReal (‖u z.1 z.2‖ ^ 2) := by
      rw [hvol, ← Measure.prod_restrict, lintegral_prod _ hGr]
    have e3 : ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) N, ENNReal.ofReal (‖w z‖ ^ 2)
        = ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) N, ENNReal.ofReal (‖u z.1 z.2‖ ^ 2) := by
      refine lintegral_congr_ae (ae_restrict_of_ae (heq.mono fun z hz => ?_))
      simp only at hz ⊢
      rw [hz]
    rw [e1, e3, ← e2]
    exact lt_of_le_of_lt (lintegral_mono_set Set.Ioc_subset_Icc_self) (hfin N)
  filter_upwards [ae_lintegral_orbit_lt_top _ hF hfinF, ae_orbit heq] with p hp hpe
  have hm0 := hw.comp_measurable (continuous_orbit p).measurable
  have hmem : MemLp (fun θ : ℝ × ℝ => w (θ.1, axialRot θ.2 (planePoint p))) 2 boxMeasure := by
    have hae : AEStronglyMeasurable (fun θ : ℝ × ℝ => w (θ.1, axialRot θ.2 (planePoint p))) boxMeasure :=
      hm0.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hae]
    refine ⟨hae.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun θ => by positivity)]
    exact hp
  refine hmem.ae_eq (boxMeasure_ac.ae_le ?_)
  filter_upwards [hpe] with θ hθ
  exact hθ.symm

end Internal.MeanStretch

end Bridge

end CertCell

end Breakdown
