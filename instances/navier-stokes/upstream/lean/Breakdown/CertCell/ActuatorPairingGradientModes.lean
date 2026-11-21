import Breakdown.CertCell.TopStatements
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.CoerciveSmoothApproxLimitsWhole
import Breakdown.Cert.CoerciveTestDensityProof
import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.CoercivePieceField

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.ActuatorPairingGradient

open Coercive.ModeL2Internal Coercive.Internal.ModeRotation

theorem locallyIntegrable_of_square {X : ℝ → Space → Space} (hX : IsSquareField X) :
    LocallyIntegrable (fun z : ℝ × Space => X z.1 z.2) volume := by
  have hn := Cert.Internal.CoerciveBordered.locallyIntegrable_of_periodic_sq (fun σ y => ‖X σ y‖)
    hX.1.norm (fun σ y => by simp only [hX.2.1 σ y]) hX.2.2
  exact hn.mono hX.1 (Filter.Eventually.of_forall fun z => by simp)

theorem ae_off_axis : ∀ᵐ y : Space, (pointPlane y).1 ≠ 0 := by
  have hs : (volume : Measure Space)
      (LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) : Set Space) = 0 := by
    refine Measure.addHaar_submodule _ _ ?_
    intro h
    have : (EuclideanSpace.single 0 1 : Space) ∈
        LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) := by
      rw [h]; trivial
    simp at this
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) hs
  have h0 : (pointPlane y).1 = 0 := not_not.1 hy
  have h1 : y 0 ^ 2 + y 1 ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 h0
  have h2 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  simpa [LinearMap.mem_ker] using h2

theorem ae_off_axis_joint : ∀ᵐ z : ℝ × Space, (pointPlane z.2).1 ≠ 0 := by
  rw [Measure.volume_eq_prod]
  exact Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd) ae_off_axis

theorem slab_eq_restrict : slab = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
  (Coercive.PieceField.Internal.restrict_eq_prod).symm

theorem slab_prod_eq :
    slab.prod boxMeasure = ((volume : Measure (ℝ × Space)).prod boxMeasure).restrict
      ((Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ×ˢ Set.univ) := by
  rw [slab_eq_restrict, ← Measure.prod_restrict, Measure.restrict_univ]

theorem slab_prod_le : slab.prod boxMeasure ≤ (volume : Measure (ℝ × Space)).prod boxMeasure := by
  rw [slab_prod_eq]
  exact Measure.restrict_le_self

theorem integrable_orbit_norm {X : ℝ → Space → Space} (hX : IsSquareField X) (R : ℝ) :
    Integrable (fun w : (ℝ × Space) × (ℝ × ℝ) =>
      (Set.Icc (-2 : ℝ) 3 ×ˢ Metric.closedBall (0 : Space) R).indicator (fun z : ℝ × Space => ‖X z.1 z.2‖)
        (orbitMap w.2 w.1)) ((volume : Measure (ℝ × Space)).prod boxMeasure) := by
  set S : Set (ℝ × Space) := Set.Icc (-2 : ℝ) 3 ×ˢ Metric.closedBall (0 : Space) R with hSdef
  have hSm : MeasurableSet S := measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hSfin : (volume : Measure (ℝ × Space)) S ≠ ⊤ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).measure_lt_top.ne
  have hfin : IsFiniteMeasure ((volume : Measure (ℝ × Space)).restrict S) := isFiniteMeasure_restrict.2 hSfin
  have hL2 : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 ((volume : Measure (ℝ × Space)).restrict S) := by
    have h := (Coercive.Internal.SmoothApprox.period_indicator_memLp hX.1 hX.2.1 hX.2.2).restrict S
    refine h.ae_eq ?_
    filter_upwards [ae_restrict_mem hSm] with z hz
    exact Set.indicator_of_mem (Set.mk_mem_prod hz.1 (Set.mem_univ _)) _
  have hu : Integrable (S.indicator (fun z : ℝ × Space => ‖X z.1 z.2‖)) volume := by
    rw [integrable_indicator_iff hSm]
    exact (hL2.integrable one_le_two).norm
  have h2 : Integrable (fun w : (ℝ × ℝ) × (ℝ × Space) => S.indicator (fun z : ℝ × Space => ‖X z.1 z.2‖) w.2)
      (boxMeasure.prod volume) := by
    have := (integrable_const (1 : ℝ) (μ := boxMeasure)).mul_prod hu
    simpa using this
  have hS : MeasurePreserving (fun w : (ℝ × ℝ) × (ℝ × Space) => (w.1, orbitMap w.1 w.2))
      (boxMeasure.prod volume) (boxMeasure.prod volume) :=
    (MeasurePreserving.id boxMeasure).skew_product continuous_orbitMap.measurable
      (Filter.Eventually.of_forall fun p => (measurePreserving_orbitMap Coercive.axialRotationHolds_proof p).map_eq)
  have h3 : Integrable (fun w : (ℝ × ℝ) × (ℝ × Space) => S.indicator (fun z : ℝ × Space => ‖X z.1 z.2‖)
      (orbitMap w.1 w.2)) (boxMeasure.prod volume) :=
    (hS.integrable_comp h2.aestronglyMeasurable).2 h2
  exact integrable_swap_iff.1 h3

theorem aesm_orbit {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) :
    AEStronglyMeasurable (fun w : (ℝ × Space) × (ℝ × ℝ) =>
      axialRot (-w.2.2) (X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2))) ((volume : Measure (ℝ × Space)).prod boxMeasure) := by
  have h1 : AEStronglyMeasurable (fun w : (ℝ × Space) × (ℝ × ℝ) => X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2))
      ((volume : Measure (ℝ × Space)).prod boxMeasure) :=
    hX.comp_quasiMeasurePreserving (Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot boxMeasure)
  have h2 : AEStronglyMeasurable (fun w : (ℝ × Space) × (ℝ × ℝ) => -w.2.2)
      ((volume : Measure (ℝ × Space)).prod boxMeasure) := (continuous_snd.snd.neg).aestronglyMeasurable
  have h3 : Continuous (Function.uncurry axialRot) := Coercive.Internal.ModeRotation.continuous_axialRot
  exact h3.comp_aestronglyMeasurable₂ h2 h1

theorem integrable_orbit_pair {X Y : ℝ → Space → Space} (hX : IsSquareField X)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) {B R : ℝ}
    (hYb : ∀ σ y, ‖Y σ y‖ ≤ B) (hYR : ∀ σ y, R < ‖y‖ → Y σ y = 0) :
    Integrable (fun w : (ℝ × Space) × (ℝ × ℝ) =>
      inner ℝ (axialRot (-w.2.2) (X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2))) (Y w.1.1 w.1.2))
      (slab.prod boxMeasure) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hYb 0 0)
  have hI := ((integrable_orbit_norm hX R).mono_measure slab_prod_le).const_mul B
  have hYm : AEStronglyMeasurable (fun w : (ℝ × Space) × (ℝ × ℝ) => Y w.1.1 w.1.2)
      ((volume : Measure (ℝ × Space)).prod boxMeasure) :=
    hY.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hm := ((aesm_orbit hX.1).inner (𝕜 := ℝ) hYm).mono_measure slab_prod_le
  refine hI.mono' hm ?_
  have a1 : ∀ᵐ w ∂(slab.prod boxMeasure), w.1.1 ∈ Set.Icc (0 : ℝ) 1 :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst slab_ae_mem
  have a2 : ∀ᵐ w ∂(slab.prod boxMeasure), w.2.1 ∈ Set.Ioc (0 : ℝ) 1 := by
    have b1 : ∀ᵐ p ∂boxMeasure, p.1 ∈ Set.Ioc (0 : ℝ) 1 :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_restrict_mem measurableSet_Ioc)
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd b1
  filter_upwards [a1, a2] with w h1 h2
  by_cases hw : R < ‖w.1.2‖
  · rw [hYR _ _ hw, inner_zero_right, norm_zero]
    exact mul_nonneg hB (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
  · have hmem : orbitMap w.2 w.1 ∈ Set.Icc (-2 : ℝ) 3 ×ˢ Metric.closedBall (0 : Space) R := by
      show (w.1.1 + w.2.1, axialRot w.2.2 w.1.2) ∈ Set.Icc (-2 : ℝ) 3 ×ˢ Metric.closedBall (0 : Space) R
      refine Set.mk_mem_prod ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩ ?_
      rw [mem_closedBall_zero_iff, norm_axialRot Coercive.axialRotationHolds_proof]
      exact not_lt.1 hw
    rw [Set.indicator_of_mem hmem]
    show _ ≤ B * ‖X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2)‖
    calc ‖inner ℝ (axialRot (-w.2.2) (X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2))) (Y w.1.1 w.1.2)‖
        ≤ ‖axialRot (-w.2.2) (X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2))‖ * ‖Y w.1.1 w.1.2‖ :=
          norm_inner_le_norm (𝕜 := ℝ) _ _
      _ = ‖X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2)‖ * ‖Y w.1.1 w.1.2‖ := by
          rw [norm_axialRot Coercive.axialRotationHolds_proof]
      _ ≤ ‖X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2)‖ * B :=
          mul_le_mul_of_nonneg_left (hYb _ _) (norm_nonneg _)
      _ = B * ‖X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2)‖ := mul_comm _ _

theorem modeVel_pair_ae {X : ℝ → Space → Space} (hX : IsSquareField X) (Y : ℝ → Space → Space) (ι : ℤ × ℤ) :
    ∀ᵐ z : ℝ × Space, ∑ i : Fin 3, modeVel ι X z.1 z.2 i * ((Y z.1 z.2 i : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ p, expFactor ι p.1 p.2 *
        ((inner ℝ (axialRot (-p.2) (X (z.1 + p.1) (axialRot p.2 z.2))) (Y z.1 z.2) : ℝ) : ℂ) ∂boxMeasure := by
  filter_upwards [ae_integrable_orbit Coercive.axialRotationHolds_proof (locallyIntegrable_of_square hX)] with z hz
  have hz' : Integrable (fun p : ℝ × ℝ => X (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure := hz
  have hc : ∀ j : Fin 3, Integrable (fun p : ℝ × ℝ => expFactor ι p.1 p.2 *
      ((axialRot (-p.2) (X (z.1 + p.1) (axialRot p.2 z.2)) j : ℝ) : ℂ)) boxMeasure := by
    intro j
    have hj := integrable_velComponent Coercive.axialRotationHolds_proof hz' j
    refine hj.norm.mono' ((continuous_expFactor ι).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hj.1)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]
  have hm : ∀ j : Fin 3, modeVel ι X z.1 z.2 j = (1 / (2 * Real.pi) : ℂ) * ∫ p, expFactor ι p.1 p.2 *
      ((axialRot (-p.2) (X (z.1 + p.1) (axialRot p.2 z.2)) j : ℝ) : ℂ) ∂boxMeasure := by
    intro j
    show (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor ι τ φ * ((axialRot (-φ) (X (z.1 + τ) (axialRot φ z.2)) j : ℝ) : ℂ) = _
    rw [iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (X (z.1 + τ) (axialRot φ z.2)) j : ℝ) : ℂ))
      (hc j)]
  simp only [hm]
  have e1 : ∀ j : Fin 3, (1 / (2 * Real.pi) : ℂ) * (∫ p, expFactor ι p.1 p.2 *
      ((axialRot (-p.2) (X (z.1 + p.1) (axialRot p.2 z.2)) j : ℝ) : ℂ) ∂boxMeasure) * ((Y z.1 z.2 j : ℝ) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ p, expFactor ι p.1 p.2 *
      ((axialRot (-p.2) (X (z.1 + p.1) (axialRot p.2 z.2)) j : ℝ) : ℂ) * ((Y z.1 z.2 j : ℝ) : ℂ) ∂boxMeasure := by
    intro j
    rw [mul_assoc, integral_mul_const]
  simp only [e1, ← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum _ (fun j _ => (hc j).mul_const _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem modePair_eq {X Y : ℝ → Space → Space} (hX : IsSquareField X)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) {B R : ℝ}
    (hYb : ∀ σ y, ‖Y σ y‖ ≤ B) (hYR : ∀ σ y, R < ‖y‖ → Y σ y = 0) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => ∑ i : Fin 3, modeVel ι X z.1 z.2 i * ((Y z.1 z.2 i : ℝ) : ℂ)) slab ∧
    ∫ z, ∑ i : Fin 3, modeVel ι X z.1 z.2 i * ((Y z.1 z.2 i : ℝ) : ℂ) ∂slab =
      (1 / (2 * Real.pi) : ℂ) * ∫ p, expFactor ι p.1 p.2 *
        ((∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (axialRot (-p.2) (X (σ + p.1) (axialRot p.2 y))) (Y σ y) : ℝ) : ℂ)
        ∂boxMeasure := by
  set k : (ℝ × Space) × (ℝ × ℝ) → ℝ := fun w =>
    inner ℝ (axialRot (-w.2.2) (X (w.1.1 + w.2.1) (axialRot w.2.2 w.1.2))) (Y w.1.1 w.1.2) with hkdef
  have hk : Integrable k (slab.prod boxMeasure) := integrable_orbit_pair hX hY hYb hYR
  set K : (ℝ × Space) × (ℝ × ℝ) → ℂ := fun w => expFactor ι w.2.1 w.2.2 * ((k w : ℝ) : ℂ) with hKdef
  have hK : Integrable K (slab.prod boxMeasure) := by
    refine hk.norm.mono' (((continuous_expFactor ι).comp continuous_snd).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hk.1)) ?_
    refine Filter.Eventually.of_forall fun w => ?_
    simp only [hKdef, norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]
  have hae : (fun z : ℝ × Space => ∑ i : Fin 3, modeVel ι X z.1 z.2 i * ((Y z.1 z.2 i : ℝ) : ℂ)) =ᵐ[slab]
      fun z => (1 / (2 * Real.pi) : ℂ) * ∫ p, K (z, p) ∂boxMeasure :=
    slab_ac.ae_le (modeVel_pair_ae hX Y ι)
  have hint : Integrable (fun z : ℝ × Space => ∫ p, K (z, p) ∂boxMeasure) slab := hK.integral_prod_left
  refine ⟨(hint.const_mul _).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  congr 1
  have hK' : Integrable (Function.uncurry fun (z : ℝ × Space) (p : ℝ × ℝ) => K (z, p)) (slab.prod boxMeasure) := hK
  rw [integral_integral_swap hK']
  refine integral_congr_ae ?_
  filter_upwards [hk.prod_left_ae] with p hp
  simp only [hKdef]
  rw [integral_const_mul, integral_complex_ofReal, integral_prod _ hp]

theorem reVec_coord (m : Fin 3 → ℂ) (i : Fin 3) : Coercive.reVec m i = (m i).re := by
  simp [Coercive.reVec, unitVector, Pi.single_apply]

theorem imVec_coord (m : Fin 3 → ℂ) (i : Fin 3) : Coercive.imVec m i = (m i).im := by
  simp [Coercive.imVec, unitVector, Pi.single_apply]

theorem inner_reVec (m : Fin 3 → ℂ) (Y : Space) :
    inner ℝ (Coercive.reVec m) Y = (∑ i : Fin 3, m i * ((Y i : ℝ) : ℂ)).re := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, reVec_coord, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem inner_imVec (m : Fin 3 → ℂ) (Y : Space) :
    inner ℝ (Coercive.imVec m) Y = (∑ i : Fin 3, m i * ((Y i : ℝ) : ℂ)).im := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, imVec_coord, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem norm_reVec_sq_le (m : Fin 3 → ℂ) : ‖Coercive.reVec m‖ ^ 2 ≤ cnormSq m := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold cnormSq
  refine Finset.sum_le_sum fun i _ => ?_
  rw [reVec_coord, Real.norm_eq_abs, sq_abs, Complex.sq_norm]
  rw [sq]
  exact Complex.re_sq_le_normSq _

theorem norm_imVec_sq_le (m : Fin 3 → ℂ) : ‖Coercive.imVec m‖ ^ 2 ≤ cnormSq m := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold cnormSq
  refine Finset.sum_le_sum fun i _ => ?_
  rw [imVec_coord, Real.norm_eq_abs, sq_abs, Complex.sq_norm]
  rw [sq]
  exact Complex.im_sq_le_normSq _

theorem exists_bound_periodic {Y : ℝ → Space → Space} (hc : Continuous (fun z : ℝ × Space => Y z.1 z.2))
    (hp : IsTimePeriodic Y) {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → Y σ y = 0) : ∃ B, ∀ σ y, ‖Y σ y‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    (f := fun z : ℝ × Space => Y z.1 z.2) hc.continuousOn
  refine ⟨max C 0, fun σ y => ?_⟩
  by_cases hy : R < ‖y‖
  · rw [hR σ y hy, norm_zero]
    exact le_max_right _ _
  · have hper : Function.Periodic (fun s => Y s y) 1 := fun s => hp s y
    have e : Y σ y = Y (Int.fract σ) y := by
      have h := Function.Periodic.sub_int_mul_eq hper (x := σ) ⌊σ⌋
      simp only [mul_one] at h
      rw [Int.fract, h]
    rw [e]
    refine (hC (Int.fract σ, y) (Set.mk_mem_prod ⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩ ?_)).trans
      (le_max_left _ _)
    rw [mem_closedBall_zero_iff]
    exact not_lt.1 hy

theorem modeVel_periodic {X : ℝ → Space → Space} (hX : IsTimePeriodic X) (ι : ℤ × ℤ) :
    IsTimePeriodic (modeVel ι X) := by
  intro σ y
  have e : (fun (τ φ : ℝ) (i : Fin 3) => axialRot (-φ) (X (σ + 1 + τ) (axialRot φ y)) i) =
      fun τ φ i => axialRot (-φ) (X (σ + τ) (axialRot φ y)) i := by
    funext τ φ i
    rw [show σ + 1 + τ = σ + τ + 1 by ring, hX]
  show modeAverage ι (fun (τ φ : ℝ) (i : Fin 3) => axialRot (-φ) (X (σ + 1 + τ) (axialRot φ y)) i) =
    modeAverage ι (fun (τ φ : ℝ) (i : Fin 3) => axialRot (-φ) (X (σ + τ) (axialRot φ y)) i)
  rw [e]

theorem aesm_reVec_modeVel {Q : ℝ → Space → Space} (hQ : AEStronglyMeasurable (fun z : ℝ × Space => Q z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEStronglyMeasurable (fun z : ℝ × Space => Coercive.reVec (modeVel ι Q z.1 z.2)) volume := by
  have h : ∀ i : Fin 3, AEStronglyMeasurable
      (fun z : ℝ × Space => (modeVel ι Q z.1 z.2 i).re • unitVector i) volume := fun i =>
    (Complex.continuous_re.comp_aestronglyMeasurable (aestronglyMeasurable_modeVel hQ ι i)).smul_const (unitVector i)
  unfold Coercive.reVec
  exact Finset.aestronglyMeasurable_sum Finset.univ fun i _ => h i

theorem aesm_imVec_modeVel {Q : ℝ → Space → Space} (hQ : AEStronglyMeasurable (fun z : ℝ × Space => Q z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEStronglyMeasurable (fun z : ℝ × Space => Coercive.imVec (modeVel ι Q z.1 z.2)) volume := by
  have h : ∀ i : Fin 3, AEStronglyMeasurable
      (fun z : ℝ × Space => (modeVel ι Q z.1 z.2 i).im • unitVector i) volume := fun i =>
    (Complex.continuous_im.comp_aestronglyMeasurable (aestronglyMeasurable_modeVel hQ ι i)).smul_const (unitVector i)
  unfold Coercive.imVec
  exact Finset.aestronglyMeasurable_sum Finset.univ fun i _ => h i

theorem periodLIntegral_cnormSq_lt_top {Q : ℝ → Space → Space} (hQ : IsSquareField Q) (ι : ℤ × ℤ) :
    periodLIntegral (fun σ y => cnormSq (modeVel ι Q σ y)) < ⊤ := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι Q z.1 z.2)) slab :=
    (aestronglyMeasurable_cnormSq (fun i => aestronglyMeasurable_modeVel hQ.1 ι i)).mono_ac slab_ac
  rw [periodLIntegral_eq_slab _ hm]
  exact lt_top_iff_ne_top.2 ((lintegral_ofReal_ne_top_iff_integrable hm
    (Filter.Eventually.of_forall fun z => cnormSq_nonneg _)).2
    (integrable_cnormSq_modeVel CoerciveWeak.modeSquareSumHolds_closed hQ ι))

theorem periodLIntegral_le_of {f g : ℝ → Space → ℝ} (h : ∀ σ y, f σ y ≤ g σ y) :
    periodLIntegral f ≤ periodLIntegral g := by
  unfold periodLIntegral
  exact lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (h σ y)

theorem re_pairing_eq {f : ℝ × Space → ℂ} (hf : Integrable f slab) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (f (σ, y)).re = (∫ z, f z ∂slab).re := by
  rw [← integral_prod (fun z => (f z).re) hf.re]
  have h := integral_re hf
  simpa only [RCLike.re_to_complex] using h

theorem im_pairing_eq {f : ℝ × Space → ℂ} (hf : Integrable f slab) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (f (σ, y)).im = (∫ z, f z ∂slab).im := by
  rw [← integral_prod (fun z => (f z).im) hf.im]
  have h := integral_im hf
  simpa only [RCLike.im_to_complex] using h

theorem solenoidalPart_modeVel_ae_zero {F Q : ℝ → Space → Space} (hF : IsSquareField F) (hQ : Coercive.IsSolenoidalPartOf F Q)
    (hmove : ∀ τ φ, Coercive.IsSolenoidalPartOf (fun σ y => axialRot (-φ) (F (σ + τ) (axialRot φ y)))
      (fun σ y => axialRot (-φ) (Q (σ + τ) (axialRot φ y))))
    (ι : ℤ × ℤ) (hFι : ∀ᵐ z : ℝ × Space, modeVel ι F z.1 z.2 = 0) :
    ∀ᵐ z : ℝ × Space, modeVel ι Q z.1 z.2 = 0 := by
  have hQs : IsSquareField Q := Coercive.PairingSplitInternal.square_of_solenoidal hQ
  have kt : ∀ ψ, IsPeriodicTestField ψ →
      Integrable (fun z : ℝ × Space => ∑ i : Fin 3, modeVel ι Q z.1 z.2 i * ((ψ z.1 z.2 i : ℝ) : ℂ)) slab ∧
      ∫ z, ∑ i : Fin 3, modeVel ι Q z.1 z.2 i * ((ψ z.1 z.2 i : ℝ) : ℂ) ∂slab = 0 := by
    intro ψ hψ
    obtain ⟨R, hR⟩ := hψ.2.2.1
    have hc : Continuous (fun z : ℝ × Space => ψ z.1 z.2) := hψ.1.continuous
    obtain ⟨B, hB⟩ := exists_bound_periodic hc hψ.2.1 hR
    have pQ := modePair_eq hQs hc.aestronglyMeasurable hB hR ι
    have pF := modePair_eq hF hc.aestronglyMeasurable hB hR ι
    refine ⟨pQ.1, ?_⟩
    rw [pQ.2]
    have e : ∀ p : ℝ × ℝ,
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (axialRot (-p.2) (Q (σ + p.1) (axialRot p.2 y))) (ψ σ y))
        = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (axialRot (-p.2) (F (σ + p.1) (axialRot p.2 y))) (ψ σ y) :=
      fun p => (hmove p.1 p.2).2.2.2.2 ψ hψ
    simp only [e]
    rw [← pF.2]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [slab_ac.ae_le hFι] with z hz
    simp [hz]
  have kg : ∀ q, IsPeriodicTestPotential q →
      Integrable (fun z : ℝ × Space => ∑ i : Fin 3, modeVel ι Q z.1 z.2 i *
        ((gradientAt (q z.1) z.2 i : ℝ) : ℂ)) slab ∧
      ∫ z, ∑ i : Fin 3, modeVel ι Q z.1 z.2 i * ((gradientAt (q z.1) z.2 i : ℝ) : ℂ) ∂slab = 0 := by
    intro q hq
    obtain ⟨R, hR⟩ := hq.2.2
    have hc : Continuous (fun z : ℝ × Space => gradientAt (q z.1) z.2) :=
      Coercive.Internal.SolenoidalPart.continuous_gradOf hq.1
    have hp : IsTimePeriodic (fun σ y => gradientAt (q σ) y) := fun σ y => by
      have e : q (σ + 1) = q σ := funext (hq.2.1 σ)
      simp only [e]
    obtain ⟨B, hB⟩ := exists_bound_periodic hc hp (Coercive.Internal.SolenoidalPart.gradOf_zero hR)
    have pQ := modePair_eq hQs hc.aestronglyMeasurable hB (Coercive.Internal.SolenoidalPart.gradOf_zero hR) ι
    refine ⟨pQ.1, ?_⟩
    rw [pQ.2]
    have e : ∀ p : ℝ × ℝ,
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (axialRot (-p.2) (Q (σ + p.1) (axialRot p.2 y)))
          (gradientAt (q σ) y)) = 0 :=
      fun p => (hmove p.1 p.2).2.2.2.1 q hq
    simp only [e, Complex.ofReal_zero, mul_zero, integral_zero]
  have hre : ∀ᵐ z : ℝ × Space, Coercive.reVec (modeVel ι Q z.1 z.2) = 0 := by
    refine Coercive.gradSolenoidalDensityHolds_proof (fun σ y => Coercive.reVec (modeVel ι Q σ y))
      (aesm_reVec_modeVel hQs.1 ι) (fun σ y => by simp only [modeVel_periodic hQs.2.1 ι σ y]) ?_ ?_ ?_
    · exact lt_of_le_of_lt (periodLIntegral_le_of fun σ y => norm_reVec_sq_le _)
        (periodLIntegral_cnormSq_lt_top hQs ι)
    · intro q hq
      obtain ⟨hi, h0⟩ := kg q hq
      simp only [inner_reVec]
      rw [re_pairing_eq hi, h0, Complex.zero_re]
    · intro ψ hψ
      obtain ⟨hi, h0⟩ := kt ψ hψ
      simp only [inner_reVec]
      rw [re_pairing_eq hi, h0, Complex.zero_re]
  have him : ∀ᵐ z : ℝ × Space, Coercive.imVec (modeVel ι Q z.1 z.2) = 0 := by
    refine Coercive.gradSolenoidalDensityHolds_proof (fun σ y => Coercive.imVec (modeVel ι Q σ y))
      (aesm_imVec_modeVel hQs.1 ι) (fun σ y => by simp only [modeVel_periodic hQs.2.1 ι σ y]) ?_ ?_ ?_
    · exact lt_of_le_of_lt (periodLIntegral_le_of fun σ y => norm_imVec_sq_le _)
        (periodLIntegral_cnormSq_lt_top hQs ι)
    · intro q hq
      obtain ⟨hi, h0⟩ := kg q hq
      simp only [inner_imVec]
      rw [im_pairing_eq hi, h0, Complex.zero_im]
    · intro ψ hψ
      obtain ⟨hi, h0⟩ := kt ψ hψ
      simp only [inner_imVec]
      rw [im_pairing_eq hi, h0, Complex.zero_im]
  filter_upwards [hre, him] with z h1 h2
  funext i
  apply Complex.ext
  · have := congrArg (fun v : Space => v i) h1
    simpa [reVec_coord] using this
  · have := congrArg (fun v : Space => v i) h2
    simpa [imVec_coord] using this

end Internal.ActuatorPairingGradient

end CertCell

end Breakdown
