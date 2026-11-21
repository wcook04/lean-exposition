import Breakdown.CertCell.BridgeStatements
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.AngularMode
import Breakdown.FracCell.RelTrace
import Breakdown.FracCell.CylinderComp
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.CertCell.TailFlipDecay

open scoped ContDiff ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.PatchModeWeak

open CellCert.CellAnalysis CellCert.CellFormula

theorem rot_plane (p : ℝ × ℝ) (φ : ℝ) : axialRot φ (planePoint p) = cylPoint p.1 φ p.2 := by
  ext i
  fin_cases i <;> simp [planePoint, cylPoint, axialRot, unitVector] <;> ring

theorem rot_frame (φ : ℝ) (u : Space) (a : Fin 3) : axialRot (-φ) u a = frameVec φ u a := by
  fin_cases a <;>
    simp [axialRot, frameVec, radialUnit, angularUnit, axialUnit, unitVector, PiLp.inner_apply,
      Fin.sum_univ_three]

theorem rot_axial (φ : ℝ) : axialRot φ (unitVector 2) = unitVector 2 := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector]

theorem phase_split (t φ : ℝ) (k : ℤ) :
    Complex.exp (-(((2 * Real.pi * t + k * φ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (-(azimuth 1 k * φ : ℝ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  simp [azimuth]
  ring

theorem planeVel_slices (η : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    planeVel η v a p.1 p.2 = ∫ τ in (0 : ℝ)..1,
      Complex.exp (-(((2 * Real.pi * η.1 * τ : ℝ) : ℂ) * Complex.I)) * modeVec 1 η.2 (v τ) p.1 p.2 a := by
  simp only [planeVel, modeVel, modeAverage, modeVec]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [show (2 * Real.pi * (η.1 : ℝ) * τ + (η.2 : ℝ) * φ) = 2 * Real.pi * ((η.1 : ℝ) * τ) + (η.2 : ℝ) * φ by ring,
    phase_split, zero_add, Prod.mk.eta, rot_plane, rot_frame]
  push_cast
  ring_nf

theorem planeHeight_slices (η : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    planeVelHeight η G 2 p.1 p.2 = ∫ τ in (0 : ℝ)..1,
      Complex.exp (-(((2 * Real.pi * η.1 * τ : ℝ) : ℂ) * Complex.I)) * gradMode 1 η.2 (G τ) 2 2 p := by
  simp only [planeVelHeight, modeGrad, modeAverage, gradMode, modeMat]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [show (2 * Real.pi * (η.1 : ℝ) * τ + (η.2 : ℝ) * φ) = 2 * Real.pi * ((η.1 : ℝ) * τ) + (η.2 : ℝ) * φ by ring,
    phase_split, zero_add, Prod.mk.eta, rot_plane, rot_axial]
  have h2 : axialRot (-φ) (G τ (cylPoint p.1 φ p.2) (unitVector 2)) 2 =
      frameMat φ (G τ (cylPoint p.1 φ p.2)) 2 2 := by
    simp [axialRot, frameMat, axialUnit, unitVector, PiLp.inner_apply]
  rw [h2]
  push_cast
  ring_nf

theorem qmp_orbit : Measure.QuasiMeasurePreserving
    (fun x : ((ℝ × ℝ) × ℝ) × ℝ => (x.1.2, cylPoint x.1.1.1 x.2 x.1.1.2))
    (((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
    ((volume : Measure ℝ).prod (volume : Measure Space)) := by
  have hΦ : Measure.QuasiMeasurePreserving (Prod.map (id : ℝ → ℝ) LowEntry.Internal.cylArg)
      ((volume : Measure ℝ).prod (volume : Measure ((ℝ × ℝ) × ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id volume)
      CylinderCompInternal.qmp_full
  have h1 : MeasurePreserving (Prod.map (Prod.swap : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ)) (id : ℝ → ℝ))
      (((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × (ℝ × ℝ)) × ℝ ≃ᵐ ℝ × ((ℝ × ℝ) × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))) :=
    measurePreserving_prodAssoc _ _ _
  exact hΦ.comp (h2.comp h1).quasiMeasurePreserving

def orbitMode {E : Type*} (X : ℝ → Space → E) (R : ℝ → E → ℂ) (x : (ℝ × ℝ) × ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), R θ (X x.2 (cylPoint x.1.1 θ x.1.2))

def box (ρ R : ℝ) : Set (ℝ × ℝ) := Icc ρ R ×ˢ Icc (-R) R

theorem aesm_orbit_kernel {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) :
    AEStronglyMeasurable (fun x : ((ℝ × ℝ) × ℝ) × ℝ => R x.2 (X x.1.2 (cylPoint x.1.1.1 x.2 x.1.1.2)))
      (((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) := by
  have h1 : AEStronglyMeasurable (fun x : ((ℝ × ℝ) × ℝ) × ℝ => X x.1.2 (cylPoint x.1.1.1 x.2 x.1.1.2))
      (((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) := by
    have := hX.comp_quasiMeasurePreserving qmp_orbit
    exact this
  exact hR.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk h1)

theorem aesm_orbitMode {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) :
    AEStronglyMeasurable (orbitMode X R) ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) := by
  have h1 := (aesm_orbit_kernel hX hR).restrict (s := univ ×ˢ Ioc (0 : ℝ) (2 * Real.pi))
  rw [← Measure.prod_restrict, Measure.restrict_univ] at h1
  have h2 := h1.integral_prod_right'
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [orbitMode]
  rw [intervalIntegral.integral_of_le (by positivity)]

theorem enorm_orbitMode_le {E : Type*} [NormedAddCommGroup E] (X : ℝ → Space → E) {R : ℝ → E → ℂ}
    (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) (x : (ℝ × ℝ) × ℝ) :
    ‖orbitMode X R x‖ₑ ≤ ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖X x.2 (cylPoint x.1.1 θ x.1.2)‖ₑ := by
  rw [orbitMode, intervalIntegral.integral_of_le (by positivity)]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun θ => ?_)
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hRb _ _)

theorem lintegral_period_shift (F : ℝ → ℝ≥0∞) (hF : ∀ θ, F (θ + 2 * Real.pi) = F θ) :
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ = ∫⁻ θ in Ioc (-Real.pi) Real.pi, F θ := by
  have hπ := Real.pi_pos
  have e1 : Ioc (0 : ℝ) (2 * Real.pi) = Ioc 0 Real.pi ∪ Ioc Real.pi (2 * Real.pi) :=
    (Ioc_union_Ioc_eq_Ioc hπ.le (by linarith)).symm
  have e2 : Ioc (-Real.pi) Real.pi = Ioc (-Real.pi) 0 ∪ Ioc 0 Real.pi :=
    (Ioc_union_Ioc_eq_Ioc (by linarith) hπ.le).symm
  have hshift : ∫⁻ θ in Ioc Real.pi (2 * Real.pi), F θ = ∫⁻ θ in Ioc (-Real.pi) 0, F θ := by
    have hmp := measurePreserving_add_right (volume : Measure ℝ) (2 * Real.pi)
    have hemb : MeasurableEmbedding (fun x : ℝ => x + 2 * Real.pi) := measurableEmbedding_addRight _
    have h := hmp.setLIntegral_comp_preimage_emb hemb F (Ioc Real.pi (2 * Real.pi))
    rw [Set.preimage_add_const_Ioc, show Real.pi - 2 * Real.pi = -Real.pi by ring, sub_self] at h
    simp only [hF] at h
    exact h.symm
  rw [e1, e2, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), hshift, add_comm]

theorem cyl_period (r z θ : ℝ) : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
  simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem box_sub {ρ R : ℝ} (hρ : 0 < ρ) : box ρ R ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
  fun _ hp => ⟨lt_of_lt_of_le hρ hp.1.1, mem_univ _⟩

theorem cyl_mem_ball {ρ R : ℝ} (hρ : 0 < ρ) {p : ℝ × ℝ} (hp : p ∈ box ρ R) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) (3 * R) := by
  refine Breakdown.CellCert.CellEnergy.Internal.CircleWeak.cyl_mem ?_
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  rw [abs_of_pos (lt_of_lt_of_le hρ h1)]
  have : |p.2| ≤ R := abs_le.2 ⟨h3, h4⟩
  linarith

theorem box_orbit_le {h : Space → ℝ≥0∞} (hh : AEMeasurable h volume) {ρ R : ℝ} (hρ : 0 < ρ) :
    ∫⁻ p in box ρ R, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), h (cylPoint p.1 θ p.2) ≤
      ENNReal.ofReal ρ⁻¹ * ∫⁻ y in Metric.closedBall (0 : Space) (3 * R), h y := by
  set H : Space → ℝ≥0∞ := (Metric.closedBall (0 : Space) (3 * R)).indicator h with hH
  have step : ∀ p ∈ box ρ R, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), h (cylPoint p.1 θ p.2) ≤
      ENNReal.ofReal ρ⁻¹ * ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * H (cylPoint p.1 θ p.2) := by
    intro p hp
    rw [lintegral_period_shift (fun θ => h (cylPoint p.1 θ p.2)) (fun θ => by simp only [cyl_period]),
      setLIntegral_congr Ioo_ae_eq_Ioc.symm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun θ => ?_
    rw [hH, indicator_of_mem (cyl_mem_ball hρ hp θ), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have : 1 ≤ ρ⁻¹ * p.1 := by
      rw [inv_mul_eq_div, le_div_iff₀ hρ, one_mul]
      exact hp.1.1
    calc h (cylPoint p.1 θ p.2) = 1 * h (cylPoint p.1 θ p.2) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (ρ⁻¹ * p.1) * h (cylPoint p.1 θ p.2) := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal this
  calc ∫⁻ p in box ρ R, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), h (cylPoint p.1 θ p.2)
      ≤ ∫⁻ p in box ρ R, ENNReal.ofReal ρ⁻¹ *
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * H (cylPoint p.1 θ p.2) :=
        setLIntegral_mono' (measurableSet_Icc.prod measurableSet_Icc) step
    _ = ENNReal.ofReal ρ⁻¹ * ∫⁻ p in box ρ R,
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * H (cylPoint p.1 θ p.2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ρ⁻¹ * ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 * H (cylPoint p.1 θ p.2) := by
        gcongr
        exact box_sub hρ
    _ ≤ ENNReal.ofReal ρ⁻¹ * ∫⁻ x in Internal.RelTrace.region,
          ENNReal.ofReal x.1.1 * H (Internal.RelTrace.cylF x) := by
        gcongr
        have e : volume.restrict Internal.RelTrace.region =
            (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
          rw [Measure.prod_restrict]
          rfl
        have hm : AEMeasurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * H (Internal.RelTrace.cylF x))
            (volume.restrict Internal.RelTrace.region) :=
          (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
            ((hh.indicator Metric.isClosed_closedBall.measurableSet).comp_quasiMeasurePreserving
              Internal.RelTrace.qmp_region)
        rw [e] at hm ⊢
        rw [lintegral_prod _ hm]
        exact le_rfl
    _ = ENNReal.ofReal ρ⁻¹ * ∫⁻ y in Metric.closedBall (0 : Space) (3 * R), h y := by
        rw [Internal.RelTrace.lintegral_cyl, hH, lintegral_indicator Metric.isClosed_closedBall.measurableSet]

theorem prod_restrict_right (s : Set ℝ) :
    ((volume : Measure (ℝ × ℝ)).prod (volume.restrict s)) =
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).restrict (univ ×ˢ s) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

theorem slab_lintegral_lt_top {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hXl : LocallyIntegrable (fun z : ℝ × Space => X z.1 z.2) volume) (R : ℝ) :
    ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ‖X τ y‖ₑ < ⊤ := by
  have hK := hXl.integrableOn_isCompact ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : Space) R))
  have hfin := hK.2
  rw [hasFiniteIntegral_iff_enorm] at hfin
  have e : ∫⁻ z in Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖X z.1 z.2‖ₑ =
      ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ‖X τ y‖ₑ := by
    rw [Measure.volume_eq_prod]
    exact setLIntegral_prod _ (hXm.enorm.restrict)
  rw [e] at hfin
  exact lt_of_le_of_lt (lintegral_mono_set Ioc_subset_Icc_self) hfin

theorem integrable_orbitMode {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hXl : LocallyIntegrable (fun z : ℝ × Space => X z.1 z.2) volume) {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) {ρ Rb : ℝ} (hρ : 0 < ρ)
    {w : ℝ × ℝ → ℂ} (hw : AEStronglyMeasurable w volume) {C : ℝ} (hwb : ∀ p, ‖w p‖ ≤ C)
    (hws : ∀ p, p ∉ box ρ Rb → w p = 0) :
    Integrable (fun x : (ℝ × ℝ) × ℝ => w x.1 * orbitMode X R x)
      ((volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hwb 0)
  refine ⟨?_, ?_⟩
  · rw [prod_restrict_right]
    exact ((hw.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst)).mul
      (aesm_orbitMode hXm hR)).restrict
  rw [hasFiniteIntegral_iff_enorm]
  set B : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal C * (box ρ Rb).indicator 1 x.1 *
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖X x.2 (cylPoint x.1.1 θ x.1.2)‖ₑ with hB
  have hpt : ∀ x : (ℝ × ℝ) × ℝ, ‖w x.1 * orbitMode X R x‖ₑ ≤ B x := by
    intro x
    by_cases hx : x.1 ∈ box ρ Rb
    · simp only [hB]
      rw [indicator_of_mem hx, Pi.one_apply, mul_one, enorm_mul]
      gcongr
      · rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hwb _)
      · exact enorm_orbitMode_le X hRb x
    · rw [hws _ hx, zero_mul, enorm_zero]
      exact zero_le
  have hslice : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      AEMeasurable (fun y => ‖X τ y‖ₑ) volume := by
    have h := hXm.prodMk_left
    exact ae_restrict_of_ae (h.mono fun τ hτ => hτ.enorm)
  calc ∫⁻ x, ‖w x.1 * orbitMode X R x‖ₑ ∂((volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1)))
      ≤ ∫⁻ x, B x ∂((volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := lintegral_mono hpt
    _ = ∫⁻ x, B x.swap ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure (ℝ × ℝ))) :=
        (lintegral_prod_swap B).symm
    _ ≤ ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ p, B (p, τ) := lintegral_prod_le _
    _ ≤ ∫⁻ τ in Ioc (0 : ℝ) 1, ENNReal.ofReal C * (ENNReal.ofReal ρ⁻¹ *
          ∫⁻ y in Metric.closedBall (0 : Space) (3 * Rb), ‖X τ y‖ₑ) := by
        refine lintegral_mono_ae (hslice.mono fun τ hτ => ?_)
        simp only [hB]
        simp_rw [mul_assoc]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        have e : ∀ p : ℝ × ℝ, (box ρ Rb).indicator 1 p *
            ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖X τ (cylPoint p.1 θ p.2)‖ₑ =
            (box ρ Rb).indicator (fun p => ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖X τ (cylPoint p.1 θ p.2)‖ₑ) p := by
          intro p
          by_cases hp : p ∈ box ρ Rb
          · simp [indicator_of_mem hp]
          · simp [indicator_of_notMem hp]
        simp_rw [e]
        rw [lintegral_indicator (show MeasurableSet (box ρ Rb) from measurableSet_Icc.prod measurableSet_Icc)]
        exact box_orbit_le hτ hρ
    _ = ENNReal.ofReal C * ENNReal.ofReal ρ⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) 1,
          ∫⁻ y in Metric.closedBall (0 : Space) (3 * Rb), ‖X τ y‖ₑ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          mul_assoc]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (slab_lintegral_lt_top hXm hXl _)

theorem loc_col {g : Space → (Space →L[ℝ] Space)} (hg : LocallyIntegrable g volume) (i : Fin 3) :
    LocallyIntegrable (fun y => g y (unitVector i)) volume :=
  locallyIntegrable_iff.2 fun _ hK => (hg.integrableOn_isCompact hK).apply_continuousLinearMap (unitVector i)

theorem weak_scalar {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient f g)
    (l : Fin 3) (φ : Space → ℝ) (hφ : SteadyCert.IsTestScalar φ) (j : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector j) * Internal.AngularMode.fc f l y =
      -∫ y, φ y * inner ℝ (Internal.AngularMode.gc g l y) (unitVector j) := by
  have hw' := hw.2.2 φ ⟨hφ.1, hφ.2⟩ j
  have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
  have hi1 := hw.1.integrable_smul_left_of_hasCompactSupport hcont hsupp
  have hi2 := (loc_col hw.2.1 j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
  calc ∫ y, fderiv ℝ φ y (unitVector j) * Internal.AngularMode.fc f l y
      = ∫ y, L (fderiv ℝ φ y (unitVector j) • f y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp [L, Internal.AngularMode.fc, innerSL_apply_apply, real_inner_comm]
    _ = L (∫ y, fderiv ℝ φ y (unitVector j) • f y) := L.integral_comp_comm hi1
    _ = -L (∫ y, φ y • g y (unitVector j)) := by rw [hw', map_neg, neg_neg]
    _ = -∫ y, L (φ y • g y (unitVector j)) := by rw [L.integral_comp_comm hi2]
    _ = -∫ y, φ y * inner ℝ (Internal.AngularMode.gc g l y) (unitVector j) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [Internal.AngularMode.gc_inner]
        simp [L, innerSL_apply_apply, real_inner_comm, unitVector]

theorem slice_angular {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient f g) (k : ℤ) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → (p.1 : ℂ) * gradMode 1 k g 1 1 p =
      ((azimuth 1 k : ℂ) * Complex.I) * modeVec 1 k f p.1 p.2 1 + modeVec 1 k f p.1 p.2 0 := by
  have locf : ∀ l, LocallyIntegrable (Internal.AngularMode.fc f l) volume := fun l =>
    Internal.AngularMode.loc_inner hw.1 (unitVector l)
  have locg : ∀ l, LocallyIntegrable (Internal.AngularMode.gc g l) volume := by
    intro l
    unfold Internal.AngularMode.gc
    refine locallyIntegrable_finsetSum Finset.univ fun i _ => ?_
    exact locallyIntegrable_iff.2 fun K hK =>
      ((Internal.AngularMode.loc_inner (loc_col hw.2.1 i) (unitVector l)).integrableOn_isCompact hK).smul_const _
  have hK := fun l => Breakdown.CellCert.CellEnergy.circleWeak (Internal.AngularMode.fc f l) (Internal.AngularMode.gc g l)
    (locf l) (locg l) (weak_scalar hw l)
  have hk : azimuth 1 k = ((k * 1 : ℤ) : ℝ) := by simp [azimuth]
  have hint := Filter.eventually_all.2 fun l => (hK l).1
  have hid := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun l =>
    (hK l).2 (Internal.AngularMode.wt (azimuth 1 k) a l) (Internal.AngularMode.wt_smooth _ a l)
      (hk ▸ Internal.AngularMode.wt_periodic _ a l)
  filter_upwards [hint, hid] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  exact (Internal.AngularMode.point 1 k f g r z (fun l => (h1 l hr).1) (fun l => (h1 l hr).2)
    (fun a l => h2 a l hr)).2.1

theorem radial_eq (θ : ℝ) : radialUnit θ = Real.cos θ • unitVector 0 + Real.sin θ • unitVector 1 := by
  ext i; fin_cases i <;> simp [radialUnit, unitVector]

theorem angular_eq (θ : ℝ) : angularUnit θ = (-Real.sin θ) • unitVector 0 + Real.cos θ • unitVector 1 := by
  ext i; fin_cases i <;> simp [angularUnit, unitVector]

theorem frameMat_trace (θ : ℝ) (M : Space →L[ℝ] Space) :
    ∑ a : Fin 3, frameMat θ M a a = ∑ i : Fin 3, M (unitVector i) i := by
  have hr := radial_eq θ
  have ha := angular_eq θ
  have hz : axialUnit = unitVector 2 := rfl
  simp only [frameMat, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hr, ha, hz, map_add, map_smul, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, unitVector]
  simp
  linear_combination ((M (EuclideanSpace.single 0 1)).ofLp 0 + (M (EuclideanSpace.single 1 1)).ofLp 1) *
    Real.sin_sq_add_cos_sq θ

theorem ae_orbit_integrable {E : Type*} [NormedAddCommGroup E] {f : Space → E} (hl : LocallyIntegrable f volume) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → IntegrableOn (fun θ => f (cylPoint p.1 θ p.2)) (Ioc (0 : ℝ) (2 * Real.pi)) := by
  have hm := hl.aestronglyMeasurable
  have hK : AEStronglyMeasurable (fun x : (ℝ × ℝ) × ℝ => f (cylPoint x.1.1 x.2 x.1.2))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) :=
    hm.comp_quasiMeasurePreserving CylinderCompInternal.qmp_full
  have hsl := hK.prodMk_left
  have hfin : ∀ n : ℕ, ∀ᵐ p : ℝ × ℝ, p ∈ box (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) →
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖f (cylPoint p.1 θ p.2)‖ₑ < ⊤ := by
    intro n
    have hρ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hS : MeasurableSet (box (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := measurableSet_Icc.prod measurableSet_Icc
    have hb := box_orbit_le (h := fun y => ‖f y‖ₑ) hm.enorm (R := (n : ℝ) + 1) hρ
    have hball : ∫⁻ y in Metric.closedBall (0 : Space) (3 * ((n : ℝ) + 1)), ‖f y‖ₑ < ⊤ := by
      have h2 := (hl.integrableOn_isCompact (isCompact_closedBall (0 : Space) (3 * ((n : ℝ) + 1)))).2
      rwa [hasFiniteIntegral_iff_enorm] at h2
    have hlt := lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hball)
    have hmeas : AEMeasurable (fun p : ℝ × ℝ => ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖f (cylPoint p.1 θ p.2)‖ₑ)
        (volume.restrict (box (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))) := by
      have h1 := hK.enorm.restrict (s := box (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ
        Ioc (0 : ℝ) (2 * Real.pi))
      rw [← Measure.prod_restrict] at h1
      exact h1.lintegral_prod_right'
    have h3 := ae_lt_top' hmeas hlt.ne
    exact (ae_restrict_iff' hS).1 h3
  filter_upwards [ae_all_iff.2 hfin, hsl] with p hp hps hr
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / p.1) (max p.1 |p.2|))
  have hn1 : 1 / p.1 < (n : ℝ) + 1 := lt_of_le_of_lt (le_max_left _ _) (hn.trans (lt_add_one _))
  have hn2 : p.1 ≤ (n : ℝ) + 1 := by
    have := le_trans (le_max_left _ _) (le_max_right (1 / p.1) (max p.1 |p.2|)); linarith
  have hn3 : |p.2| ≤ (n : ℝ) + 1 := by
    have := le_trans (le_max_right _ _) (le_max_right (1 / p.1) (max p.1 |p.2|)); linarith
  have hmem : p ∈ box (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    refine ⟨⟨?_, hn2⟩, (abs_le.1 hn3).1, (abs_le.1 hn3).2⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hr] at hn1
    linarith
  refine ⟨hps.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact hp n hmem

def velEvaluator (k : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) : ℂ :=
  Complex.exp (-(azimuth 1 k * θ : ℝ) * Complex.I) * (frameVec θ u a : ℂ)

def gradEvaluator (k : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-(azimuth 1 k * θ : ℝ) * Complex.I) * (frameMat θ M a b : ℂ)

theorem norm_radialUnit (θ : ℝ) : ‖radialUnit θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [radialUnit, Fin.sum_univ_three, Real.cos_sq_add_sin_sq]

theorem norm_angularUnit (θ : ℝ) : ‖angularUnit θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [angularUnit, Fin.sum_univ_three, Real.sin_sq_add_cos_sq]

theorem norm_axialUnit : ‖axialUnit‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [axialUnit]

theorem norm_frameUnit (θ : ℝ) (a : Fin 3) : ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a‖ = 1 := by
  fin_cases a
  · exact norm_radialUnit θ
  · exact norm_angularUnit θ
  · exact norm_axialUnit

theorem continuous_frameUnit (a : Fin 3) :
    Continuous (fun θ : ℝ => (![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a) := by
  fin_cases a
  · show Continuous (fun θ : ℝ => radialUnit θ)
    simp only [radial_eq]
    fun_prop
  · show Continuous (fun θ : ℝ => angularUnit θ)
    simp only [angular_eq]
    fun_prop
  · exact continuous_const

theorem frameVec_unit (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ u a = inner ℝ u ((![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a) := by
  fin_cases a <;> rfl

theorem phase_norm (k : ℤ) (θ : ℝ) : ‖Complex.exp (-(azimuth 1 k * θ : ℝ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem velEvaluator_le (k : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) : ‖velEvaluator k a θ u‖ ≤ ‖u‖ := by
  rw [velEvaluator, norm_mul, phase_norm, one_mul, Complex.norm_real, frameVec_unit]
  calc ‖inner ℝ u ((![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a)‖
      ≤ ‖u‖ * ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a‖ := norm_inner_le_norm _ _
    _ = ‖u‖ := by rw [norm_frameUnit, mul_one]

theorem gradEvaluator_le (k : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) : ‖gradEvaluator k a b θ M‖ ≤ ‖M‖ := by
  rw [gradEvaluator, norm_mul, phase_norm, one_mul, Complex.norm_real]
  calc ‖frameMat θ M a b‖ ≤ ‖M ((![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b)‖ *
        ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a‖ := norm_inner_le_norm _ _
    _ ≤ ‖M‖ * ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b‖ *
        ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a‖ := by
      gcongr
      exact M.le_opNorm _
    _ = ‖M‖ := by rw [norm_frameUnit, norm_frameUnit, mul_one, mul_one]

theorem phase_cont (k : ℤ) : Continuous (fun θ : ℝ => Complex.exp (-(azimuth 1 k * θ : ℝ) * Complex.I)) := by
  fun_prop

theorem velEvaluator_cont (k : ℤ) (a : Fin 3) : Continuous (fun q : ℝ × Space => velEvaluator k a q.1 q.2) := by
  unfold velEvaluator
  simp only [frameVec_unit]
  exact ((phase_cont k).comp continuous_fst).mul (Complex.continuous_ofReal.comp
    (continuous_snd.inner ((continuous_frameUnit a).comp continuous_fst)))

theorem gradEvaluator_cont (k : ℤ) (a b : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space) => gradEvaluator k a b q.1 q.2) := by
  unfold gradEvaluator frameMat
  exact ((phase_cont k).comp continuous_fst).mul (Complex.continuous_ofReal.comp
    ((continuous_snd.clm_apply ((continuous_frameUnit b).comp continuous_fst)).inner
      ((continuous_frameUnit a).comp continuous_fst)))

theorem modeVec_evaluator (k : ℤ) (f : Space → Space) (r z : ℝ) (a : Fin 3) :
    modeVec 1 k f r z a = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), velEvaluator k a θ (f (cylPoint r θ z)) := rfl

theorem gradMode_evaluator (k : ℤ) (g : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    gradMode 1 k g a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), gradEvaluator k a b θ (g (cylPoint p.1 θ p.2)) := rfl

theorem ii_evaluator {E : Type*} [NormedAddCommGroup E] {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) {F : ℝ → E}
    (hF : IntegrableOn F (Ioc (0 : ℝ) (2 * Real.pi))) :
    IntervalIntegrable (fun θ => R θ (F θ)) volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  refine Integrable.mono' hF.norm ?_ (Filter.Eventually.of_forall fun θ => hRb θ (F θ))
  exact hR.comp_aestronglyMeasurable (measurable_id.aestronglyMeasurable.prodMk hF.aestronglyMeasurable)

theorem slice_trace {g : Space → (Space →L[ℝ] Space)} (hl : LocallyIntegrable g volume)
    (hdiv : ∀ᵐ y, ∑ i : Fin 3, g y (unitVector i) i = 0) (k : ℤ) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → gradMode 1 k g 0 0 p + gradMode 1 k g 1 1 p + gradMode 1 k g 2 2 p = 0 := by
  have hZ : ∀ᵐ p : ℝ × ℝ, ∀ᵐ θ : ℝ, ∑ i : Fin 3, g (cylPoint p.1 θ p.2) (unitVector i) i = 0 := by
    have h1 := CylinderCompInternal.qmp_full.ae hdiv
    exact Measure.ae_ae_of_ae_prod h1
  filter_upwards [ae_orbit_integrable hl, hZ] with p hp hz hr
  have hii := fun a b => ii_evaluator (gradEvaluator_cont k a b) (gradEvaluator_le k a b) (hp hr)
  simp only [gradMode_evaluator]
  rw [← mul_add, ← mul_add, ← intervalIntegral.integral_add (hii 0 0) (hii 1 1),
    ← intervalIntegral.integral_add ((hii 0 0).add (hii 1 1)) (hii 2 2)]
  have hzero : ∫ θ in (0 : ℝ)..(2 * Real.pi), (gradEvaluator k 0 0 θ (g (cylPoint p.1 θ p.2)) +
      gradEvaluator k 1 1 θ (g (cylPoint p.1 θ p.2)) + gradEvaluator k 2 2 θ (g (cylPoint p.1 θ p.2))) = 0 := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine integral_eq_zero_of_ae ((ae_restrict_of_ae hz).mono fun θ hθ => ?_)
    simp only [gradEvaluator, ← mul_add]
    have ht := frameMat_trace θ (g (cylPoint p.1 θ p.2))
    rw [Fin.sum_univ_three] at ht
    rw [hθ] at ht
    rw [show ((frameMat θ (g (cylPoint p.1 θ p.2)) 0 0 : ℝ) : ℂ) + (frameMat θ (g (cylPoint p.1 θ p.2)) 1 1 : ℝ) +
      (frameMat θ (g (cylPoint p.1 θ p.2)) 2 2 : ℝ) = ((0 : ℝ) : ℂ) by rw [← ht]; push_cast; ring]
    simp
  rw [hzero, mul_zero]

def radialEval (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  q.1 • EuclideanSpace.proj (0 : Fin 3) + q.2 • EuclideanSpace.proj (1 : Fin 3)

def axialEval (_ : ℝ × ℝ) : Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)

theorem radialEval_smooth : ContDiff ℝ ∞ radialEval :=
  (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)

theorem axialEval_smooth : ContDiff ℝ ∞ axialEval := contDiff_const

theorem radialEval_apply (θ : ℝ) (u : Space) : radialEval (Real.cos θ, Real.sin θ) u = frameVec θ u 0 := by
  simp [radialEval, frameVec, radial_eq, inner_add_right, inner_smul_right, unitVector, PiLp.inner_apply]

theorem axialEval_apply (θ : ℝ) (u : Space) : axialEval (Real.cos θ, Real.sin θ) u = frameVec θ u 2 := by
  simp [axialEval, frameVec, axialUnit, PiLp.inner_apply]

theorem radialEval_mat (θ : ℝ) (M : Space →L[ℝ] Space) :
    radialEval (Real.cos θ, Real.sin θ) (M (radialUnit θ)) = frameMat θ M 0 0 := by
  rw [radialEval_apply]
  rfl

theorem axialEval_mat (θ : ℝ) (M : Space →L[ℝ] Space) :
    axialEval (Real.cos θ, Real.sin θ) (M axialUnit) = frameMat θ M 2 2 := by
  rw [axialEval_apply]
  rfl

theorem two_pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
  have := Real.pi_pos
  exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)

theorem circle_vel (L : ℝ × ℝ → (Space →L[ℝ] ℝ)) (a : Fin 3)
    (hL : ∀ θ u, L (Real.cos θ, Real.sin θ) u = frameVec θ u a) (k : ℤ) (f : Space → Space) (p : ℝ × ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth 1 k * θ : ℝ) * Complex.I) *
      (L (Real.cos θ, Real.sin θ) (f (cylPoint p.1 θ p.2)) : ℂ) = (2 * Real.pi : ℂ) * modeVec 1 k f p.1 p.2 a := by
  rw [modeVec_evaluator, ← mul_assoc, mul_one_div_cancel two_pi_ne, one_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [velEvaluator, hL]

theorem circle_grad (L : ℝ × ℝ → (Space →L[ℝ] ℝ)) (a : Fin 3) (e : ℝ → Space)
    (hL : ∀ θ M, L (Real.cos θ, Real.sin θ) (M (e θ)) = frameMat θ M a a) (k : ℤ)
    (g : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth 1 k * θ : ℝ) * Complex.I) *
      (L (Real.cos θ, Real.sin θ) (g (cylPoint p.1 θ p.2) (e θ)) : ℂ) = (2 * Real.pi : ℂ) * gradMode 1 k g a a p := by
  rw [gradMode_evaluator, ← mul_assoc, mul_one_div_cancel two_pi_ne, one_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [gradEvaluator, hL]

theorem scale_identity {A B C D : ℝ × ℝ → ℂ} (c : ℂ) (hc : c ≠ 0) (hA : ∀ p, A p = c * C p)
    (hB : ∀ p, B p = c * D p) (w u : ℝ × ℝ → ℂ) (h : ∫ p, w p * A p = -∫ p, u p * B p) :
    ∫ p, w p * C p = -∫ p, u p * D p := by
  simp_rw [hA, hB, show ∀ p, w p * (c * C p) = c * (w p * C p) from fun p => by ring,
    show ∀ p, u p * (c * D p) = c * (u p * D p) from fun p => by ring, integral_const_mul] at h
  rw [← mul_neg] at h
  exact mul_left_cancel₀ hc h

theorem slice_weak {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient f g) (k : ℤ)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 0 =
      -∫ p, (ψ p : ℂ) * gradMode 1 k g 0 0 p) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 2 =
      -∫ p, (ψ p : ℂ) * gradMode 1 k g 2 2 p) := by
  have h3 : ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • g y (unitVector j) := by
    intro φ hφ j
    rw [hw.2.2 φ ⟨hφ.1, hφ.2⟩ j, neg_neg]
  have hr := CellCert.CellFormula.cylModeWeak Space f g hw.1 (loc_col hw.2.1) h3 radialEval radialEval_smooth
    1 k ψ hψ hc hpos
  have hz := CellCert.CellFormula.cylModeWeak Space f g hw.1 (loc_col hw.2.1) h3 axialEval axialEval_smooth
    1 k ψ hψ hc hpos
  exact ⟨scale_identity _ two_pi_ne (circle_vel radialEval 0 radialEval_apply k f)
      (circle_grad radialEval 0 radialUnit radialEval_mat k g) _ _ hr.1,
    scale_identity _ two_pi_ne (circle_vel axialEval 2 axialEval_apply k f)
      (circle_grad axialEval 2 (fun _ => axialUnit) axialEval_mat k g) _ _ hz.2⟩

theorem radial_weight_smooth {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * ψ p) :=
  contDiff_fst.mul hψ

theorem fderiv_radial_weight {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p u : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 * ψ p) p u = u.1 * ψ p + p.1 * fderiv ℝ ψ p u := by
  have hd : DifferentiableAt ℝ ψ p := (hψ.differentiable (by simp)).differentiableAt
  rw [fderiv_fun_mul differentiableAt_fst hd]
  simp [fderiv_fst]
  ring

theorem slice_div {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient f g)
    (hdiv : ∀ᵐ y, ∑ i : Fin 3, g y (unitVector i) i = 0) (k : ℤ)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1)
    (h1 : Integrable fun p : ℝ × ℝ => ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 0)
    (h3 : Integrable fun p : ℝ × ℝ => ((ψ p : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 1)
    (h4 : Integrable fun p : ℝ × ℝ => ((ψ p : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 0)
    (h5 : ∀ a, Integrable fun p : ℝ × ℝ => ((p.1 * ψ p : ℝ) : ℂ) * gradMode 1 k g a a p) :
    (∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 0) +
      (∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 2) -
      ((k : ℂ) * Complex.I) * ∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 1 = 0 := by
  have hsupp : ∀ p ∈ tsupport (fun p : ℝ × ℝ => p.1 * ψ p), 0 < p.1 := fun p hp =>
    hpos p (tsupport_mul_subset_right hp)
  have hW := slice_weak hw k (fun p : ℝ × ℝ => p.1 * ψ p) (radial_weight_smooth hψ) hc.mul_left hsupp
  simp only [fderiv_radial_weight hψ] at hW
  have hzero : ∀ p : ℝ × ℝ, ¬ 0 < p.1 → ψ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp (hpos p h))
  have hazi : (azimuth 1 k : ℂ) = (k : ℂ) := by simp [azimuth]
  have eA : (∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 0) +
      ∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 0 =
      -∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * gradMode 1 k g 0 0 p := by
    rw [← integral_add h4 h1, ← hW.1]
    congr 1
    funext p
    push_cast
    ring
  have eB : ∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 2 =
      -∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * gradMode 1 k g 2 2 p := by
    rw [← hW.2]
    congr 1
    funext p
    push_cast
    ring
  have eC : ∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * gradMode 1 k g 1 1 p =
      (k : ℂ) * Complex.I * (∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 1) +
        ∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * modeVec 1 k f p.1 p.2 0 := by
    rw [← integral_const_mul, ← integral_add (h3.const_mul _) h4]
    refine integral_congr_ae ((slice_angular hw k).mono fun p hp => ?_)
    by_cases hr : 0 < p.1
    · have e := hp hr
      rw [hazi] at e
      push_cast
      linear_combination ((ψ p : ℝ) : ℂ) * e
    · simp [hzero p hr]
  have eD : (∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * gradMode 1 k g 0 0 p) +
      (∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * gradMode 1 k g 1 1 p) +
      ∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * gradMode 1 k g 2 2 p = 0 := by
    have e1 := integral_add (h5 0) (h5 1)
    have e2 := integral_add ((h5 0).add (h5 1)) (h5 2)
    simp only [Pi.add_apply] at e2
    rw [← e1, ← e2]
    refine integral_eq_zero_of_ae ((slice_trace hw.2.1 hdiv k).mono fun p hp => ?_)
    by_cases hr : 0 < p.1
    · simp only [Pi.zero_apply]
      rw [← mul_add, ← mul_add, hp hr, mul_zero]
    · simp [hzero p hr]
  linear_combination eA + eB + eC - eD

theorem exists_box {ψ : ℝ × ℝ → ℝ} (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ∀ p, p ∉ box ρ R → p ∉ tsupport ψ := by
  by_cases hne : (tsupport ψ).Nonempty
  · obtain ⟨q, hq, hmin⟩ := hc.isCompact.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine ⟨q.1, R, hpos q hq, fun p hp hps => hp ?_⟩
    have h1 := hR hps
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at h1
    have h2 : |p.1| ≤ R := (le_max_left _ _).trans h1
    have h3 : |p.2| ≤ R := (le_max_right _ _).trans h1
    exact ⟨⟨hmin hps, (le_abs_self _).trans h2⟩, (abs_le.1 h3).1, (abs_le.1 h3).2⟩
  · exact ⟨1, 1, one_pos, fun p _ hps => hne ⟨p, hps⟩⟩

theorem weight_bound {w : ℝ × ℝ → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∃ C, ∀ p, ‖w p‖ ≤ C :=
  hw.bounded_above_of_compact_support hwc

def phase (η : ℤ × ℤ) (τ : ℝ) : ℂ := Complex.exp (-(((2 * Real.pi * η.1 * τ : ℝ) : ℂ) * Complex.I))

theorem phase_norm_le (η : ℤ × ℤ) (τ : ℝ) : ‖phase η τ * (1 / (2 * Real.pi) : ℂ)‖ ≤ 1 / (2 * Real.pi) := by
  have h1 : ‖phase η τ‖ = 1 := by
    rw [phase, Complex.norm_exp]
    simp
  have hπ := Real.pi_pos
  rw [norm_mul, h1, one_mul, show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem phase_cont' (η : ℤ × ℤ) : Continuous (phase η) := by
  unfold phase
  fun_prop

theorem swap_mode {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hXl : LocallyIntegrable (fun z : ℝ × Space => X z.1 z.2) volume) {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) {ρ Rb : ℝ} (hρ : 0 < ρ)
    {w : ℝ × ℝ → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) (hws : ∀ p, p ∉ box ρ Rb → w p = 0)
    (η : ℤ × ℤ) :
    Integrable (fun p : ℝ × ℝ => w p * ∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))) ∧
    ∫ p : ℝ × ℝ, w p * (∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))) =
      ∫ τ in Ioc (0 : ℝ) 1, phase η τ * (1 / (2 * Real.pi) : ℂ) * ∫ p : ℝ × ℝ, w p * orbitMode X R (p, τ) ∧
    Integrable (fun τ => phase η τ * (1 / (2 * Real.pi) : ℂ) * ∫ p : ℝ × ℝ, w p * orbitMode X R (p, τ))
      (volume.restrict (Ioc (0 : ℝ) 1)) ∧
    ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) 1)), Integrable (fun p : ℝ × ℝ => w p * orbitMode X R (p, τ)) := by
  obtain ⟨C, hC⟩ := weight_bound hw hwc
  have hK := integrable_orbitMode hXm hXl hR hRb hρ hw.aestronglyMeasurable hC hws
  set F : (ℝ × ℝ) × ℝ → ℂ := fun x => phase η x.2 * (1 / (2 * Real.pi) : ℂ) * (w x.1 * orbitMode X R x) with hF
  have hFi : Integrable F ((volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    hK.bdd_mul (c := 1 / (2 * Real.pi))
      (((phase_cont' η).comp continuous_snd).mul continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => phase_norm_le η x.2)
  have hpt : ∀ p : ℝ × ℝ, w p * (∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))) =
      ∫ τ in Ioc (0 : ℝ) 1, F (p, τ) := by
    intro p
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hF]
    ring
  have hpt2 : ∀ τ, ∫ p : ℝ × ℝ, F (p, τ) = phase η τ * (1 / (2 * Real.pi) : ℂ) * ∫ p : ℝ × ℝ, w p * orbitMode X R (p, τ) := by
    intro τ
    simp only [hF]
    rw [integral_const_mul]
  refine ⟨?_, ?_, ?_, hK.prod_left_ae⟩
  · simp_rw [hpt]
    exact hFi.integral_prod_left
  · simp_rw [hpt]
    rw [integral_integral_swap (f := fun p τ => F (p, τ)) hFi]
    simp_rw [hpt2]
  · simp_rw [← hpt2]
    exact hFi.integral_prod_right

theorem planeVel_orbit (η : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    planeVel η v a p.1 p.2 = ∫ τ in (0 : ℝ)..1,
      phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode v (velEvaluator η.2 a) (p, τ)) :=
  planeVel_slices η v a p

theorem planeHeight_orbit (η : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    planeVelHeight η G 2 p.1 p.2 = ∫ τ in (0 : ℝ)..1,
      phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode G (gradEvaluator η.2 2 2) (p, τ)) :=
  planeHeight_slices η G p

theorem orbit_vel (k : ℤ) (v : ℝ → Space → Space) (a : Fin 3) (p : ℝ × ℝ) (τ : ℝ) :
    orbitMode v (velEvaluator k a) (p, τ) = (2 * Real.pi : ℂ) * modeVec 1 k (v τ) p.1 p.2 a := by
  rw [modeVec_evaluator, ← mul_assoc, mul_one_div_cancel two_pi_ne, one_mul]
  rfl

theorem orbit_grad (k : ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) (τ : ℝ) :
    orbitMode G (gradEvaluator k a b) (p, τ) = (2 * Real.pi : ℂ) * gradMode 1 k (G τ) a b p := by
  rw [gradMode_evaluator, ← mul_assoc, mul_one_div_cancel two_pi_ne, one_mul]
  rfl

theorem weight_support {ψ : ℝ × ℝ → ℝ} {ρ R : ℝ} (hbox : ∀ p, p ∉ box ρ R → p ∉ tsupport ψ)
    {w : ℝ × ℝ → ℂ} (hw : ∀ p, p ∉ tsupport ψ → w p = 0) : HasCompactSupport w ∧ ∀ p, p ∉ box ρ R → w p = 0 :=
  ⟨HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) fun p hp => hw p (hbox p hp),
    fun p hp => hw p (hbox p hp)⟩

theorem fderiv_off {ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∉ tsupport ψ) (u : ℝ × ℝ) : fderiv ℝ ψ p u = 0 := by
  rw [image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_fderiv_subset ℝ h))]
  rfl

theorem int_scale {w M : ℝ × ℝ → ℂ} {om : ℝ × ℝ → ℂ} (hom : ∀ p, om p = (2 * Real.pi : ℂ) * M p)
    (h : Integrable fun p => w p * om p) : Integrable fun p => w p * M p := by
  have h2 := h.const_mul (1 / (2 * Real.pi) : ℂ)
  refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [hom]
  field_simp [two_pi_ne]

theorem integral_scale {w M : ℝ × ℝ → ℂ} {om : ℝ × ℝ → ℂ} (hom : ∀ p, om p = (2 * Real.pi : ℂ) * M p) :
    ∫ p, w p * om p = (2 * Real.pi : ℂ) * ∫ p, w p * M p := by
  rw [← integral_const_mul]
  congr 1
  funext p
  rw [hom]
  ring

theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, f x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have e2 : ∀ x, f x ^ (2 : ℝ) = f x ^ 2 := fun x => by rw [← ENNReal.rpow_natCast]; norm_num
  simp only [e2] at h
  calc (∫⁻ x, f x ∂μ) ^ 2 ≤ ((∫⁻ x, f x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * μ univ ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = μ univ * ∫⁻ x, f x ^ 2 ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num
      ring

theorem orbit_sq_bound {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    {R : ℝ → E → ℂ} (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) (η : ℤ × ℤ) {ρ Rb : ℝ} (hρ : 0 < ρ) :
    ∫⁻ p in box ρ Rb, ‖∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal ρ⁻¹ *
        ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) (3 * Rb), ‖X τ y‖ₑ ^ 2) := by
  have hπ := Real.pi_pos
  set f : (ℝ × ℝ) × ℝ → ℝ → ℝ≥0∞ := fun x θ => ‖X x.2 (cylPoint x.1.1 θ x.1.2)‖ₑ with hf
  have hK : AEMeasurable (fun y : ((ℝ × ℝ) × ℝ) × ℝ => f y.1 y.2)
      (((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) := by
    have := (hXm.comp_quasiMeasurePreserving qmp_orbit).enorm
    exact this
  have hpt : ∀ p : ℝ × ℝ, ‖∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))‖ₑ ≤
      ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ := by
    intro p
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ => ?_)
    refine le_trans ?_ (enorm_orbitMode_le X hRb (p, τ))
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖phase η τ * (1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := (phase_norm_le η τ).trans (by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three])
    calc ‖phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))‖
        = ‖phase η τ * (1 / (2 * Real.pi) : ℂ)‖ * ‖orbitMode X R (p, τ)‖ := by rw [← norm_mul, mul_assoc]
      _ ≤ 1 * ‖orbitMode X R (p, τ)‖ := by gcongr
      _ = ‖orbitMode X R (p, τ)‖ := one_mul _
  have hslice : ∀ᵐ p : ℝ × ℝ, AEStronglyMeasurable (fun q : ℝ × ℝ => X q.1 (cylPoint p.1 q.2 p.2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have h1 : AEStronglyMeasurable (fun y : (ℝ × ℝ) × (ℝ × ℝ) => X y.2.1 (cylPoint y.1.1 y.2.2 y.1.2))
        ((volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
      have hmp := (measurePreserving_prodAssoc (volume : Measure (ℝ × ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)).symm
      exact (hXm.comp_quasiMeasurePreserving qmp_orbit).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
    exact h1.prodMk_left
  have hsq : ∀ᵐ p : ℝ × ℝ, (∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ) ^ 2 ≤
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ ^ 2 := by
    filter_upwards [hslice] with p hp
    have hpr := (hp.restrict (s := Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) (2 * Real.pi)))
    rw [← Measure.prod_restrict] at hpr
    have hτ : AEMeasurable (fun τ => ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      hpr.enorm.lintegral_prod_right'
    have hθ : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        AEMeasurable (fun θ => f (p, τ) θ) (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
      hpr.prodMk_left.mono fun τ h => h.enorm
    calc (∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ) ^ 2
        ≤ volume.restrict (Ioc (0 : ℝ) 1) univ *
            ∫⁻ τ in Ioc (0 : ℝ) 1, (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ) ^ 2 :=
          sq_lintegral_le _ hτ
      _ ≤ 1 * ∫⁻ τ in Ioc (0 : ℝ) 1, ENNReal.ofReal (2 * Real.pi) *
            ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ ^ 2 := by
          refine mul_le_mul' (le_of_eq (by simp)) (lintegral_mono_ae (hθ.mono fun τ hτ' => ?_))
          refine (sq_lintegral_le _ hτ').trans (le_of_eq ?_)
          simp [Real.volume_Ioc]
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ ^ 2 := by
          rw [one_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hswap : ∫⁻ p in box ρ Rb, ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ ^ 2 =
      ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ p in box ρ Rb, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ ^ 2 := by
    refine lintegral_lintegral_swap ?_
    have := ((hK.pow_const 2).restrict (s := (box ρ Rb ×ˢ Ioc (0 : ℝ) 1) ×ˢ Ioc (0 : ℝ) (2 * Real.pi)))
    rw [← Measure.prod_restrict, ← Measure.prod_restrict] at this
    exact this.lintegral_prod_right'
  have hτs : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) 1)), AEMeasurable (fun y => ‖X τ y‖ₑ ^ 2) volume := by
    have h := hXm.prodMk_left
    exact ae_restrict_of_ae (h.mono fun τ hτ => hτ.enorm.pow_const 2)
  calc ∫⁻ p in box ρ Rb, ‖∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))‖ₑ ^ 2
      ≤ ∫⁻ p in box ρ Rb, ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ ^ 2 := by
        refine lintegral_mono_ae (ae_restrict_of_ae (hsq.mono fun p hp => ?_))
        exact (pow_le_pow_left₀ zero_le (hpt p) 2).trans hp
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ p in box ρ Rb,
          ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), f (p, τ) θ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hswap]
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ∫⁻ τ in Ioc (0 : ℝ) 1, ENNReal.ofReal ρ⁻¹ *
          ∫⁻ y in Metric.closedBall (0 : Space) (3 * Rb), ‖X τ y‖ₑ ^ 2 := by
        exact mul_le_mul' le_rfl (lintegral_mono_ae (hτs.mono fun τ hτ => box_orbit_le hτ hρ))
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem aesm_plane {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) (η : ℤ × ℤ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))) volume := by
  have h1 : AEStronglyMeasurable (fun x : (ℝ × ℝ) × ℝ => phase η x.2 * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R x))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) :=
    ((phase_cont' η).comp continuous_snd).aestronglyMeasurable.mul
      (aestronglyMeasurable_const.mul (aesm_orbitMode hXm hR))
  have h2 := h1.restrict (s := univ ×ˢ Ioc (0 : ℝ) 1)
  rw [← Measure.prod_restrict, Measure.restrict_univ] at h2
  refine h2.integral_prod_right'.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only
  rw [intervalIntegral.integral_of_le zero_le_one]

theorem memLp_plane {E : Type*} [NormedAddCommGroup E] {X : ℝ → Space → E}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hX2 : ∀ Rb : ℝ, ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) Rb, ‖X τ y‖ₑ ^ 2 < ⊤)
    {R : ℝ → E → ℂ} (hR : Continuous (fun q : ℝ × E => R q.1 q.2)) (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖)
    (η : ℤ × ℤ) {ρ Rb : ℝ} (hρ : 0 < ρ) :
    MemLp (fun p : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, phase η τ * ((1 / (2 * Real.pi) : ℂ) * orbitMode X R (p, τ))) 2
      (volume.restrict (box ρ Rb)) := by
  refine ⟨(aesm_plane hXm hR η).restrict, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have e : ∀ x : ℝ≥0∞, x ^ (ENNReal.toReal 2) = x ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast]; norm_num
  simp only [e]
  refine lt_of_le_of_lt (orbit_sq_bound hXm hRb η hρ) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hX2 _))

theorem orbit_grad_column (k : ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (x : (ℝ × ℝ) × ℝ) :
    orbitMode G (gradEvaluator k 2 2) x = orbitMode (fun τ y => G τ y (unitVector 2)) (velEvaluator k 2) x := rfl

end Internal.PatchModeWeak

open Internal.PatchModeWeak in
theorem planeVel_memLp {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ) (a : Fin 3) {ρ R : ℝ} (hρ : 0 < ρ) :
    MemLp (fun p : ℝ × ℝ => planeVel η v a p.1 p.2) 2 (volume.restrict (Icc ρ R ×ˢ Icc (-R) R)) := by
  have hX2 : ∀ Rb : ℝ, ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) Rb, ‖v τ y‖ₑ ^ 2 < ⊤ := by
    intro Rb
    have h := Coercive.Internal.PerturbationFacts.velocity_localSquare hv Rb
    refine lt_of_le_of_lt ?_ h
    refine (lintegral_mono_set Ioc_subset_Icc_self).trans (le_of_eq ?_)
    refine lintegral_congr fun τ => lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h := memLp_plane hv.measurable_velocity hX2 (velEvaluator_cont η.2 a) (velEvaluator_le η.2 a) η (Rb := R) hρ
  simp only [← planeVel_orbit] at h
  exact h

open Internal.PatchModeWeak in
theorem planeHeight_memLp {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ) {ρ R : ℝ} (hρ : 0 < ρ) :
    MemLp (fun p : ℝ × ℝ => planeVelHeight η G 2 p.1 p.2) 2 (volume.restrict (Icc ρ R ×ˢ Icc (-R) R)) := by
  have hXm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector 2)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector 2)).continuous.comp_aestronglyMeasurable hv.measurable_gradient
  have hX2 : ∀ Rb : ℝ, ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) Rb,
      ‖G τ y (unitVector 2)‖ₑ ^ 2 < ⊤ := by
    intro Rb
    refine lt_of_le_of_lt ?_ hv.gradient_finite
    refine (lintegral_mono_set Ioc_subset_Icc_self).trans (lintegral_mono fun τ => ?_)
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact Finset.single_le_sum (f := fun i => ‖G τ y (unitVector i)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ 2)
  have h := memLp_plane hXm hX2 (velEvaluator_cont η.2 2) (velEvaluator_le η.2 2) η (Rb := R) hρ
  simp only [← orbit_grad_column, ← planeHeight_orbit] at h
  exact h

open Internal.PatchModeWeak in
theorem planeVel_divergence_weak {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ) (ψ : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    (∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * planeVel η v 0 p.1 p.2) +
      (∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * planeVel η v 2 p.1 p.2) -
      ((η.2 : ℂ) * Complex.I) * ∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * planeVel η v 1 p.1 p.2 = 0 := by
  obtain ⟨ρ, R, hρ, hbox⟩ := exists_box hc hpos
  have hvm := hv.measurable_velocity
  have hvl := Coercive.Internal.PerturbationFacts.velocity_locallyIntegrable hv
  have hGm := hv.measurable_gradient
  have hGl := Coercive.Internal.PerturbationFacts.gradient_locallyIntegrable hv
  set k := η.2 with hk
  have hd : Continuous (fun p => fderiv ℝ ψ p) := hψ.continuous_fderiv (by simp)
  have c0 : Continuous (fun p : ℝ × ℝ => ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.mul (hd.clm_apply continuous_const))
  have c2 : Continuous (fun p : ℝ × ℝ => ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.mul (hd.clm_apply continuous_const))
  have c1 : Continuous (fun p : ℝ × ℝ => ((ψ p : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hψ.continuous
  have cr : Continuous (fun p : ℝ × ℝ => ((p.1 * ψ p : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.mul hψ.continuous)
  have z0 := weight_support hbox (w := fun p : ℝ × ℝ => ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ))
    (fun p hp => by simp [fderiv_off hp])
  have z2 := weight_support hbox (w := fun p : ℝ × ℝ => ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ))
    (fun p hp => by simp [fderiv_off hp])
  have z1 := weight_support hbox (w := fun p : ℝ × ℝ => ((ψ p : ℝ) : ℂ))
    (fun p hp => by simp [image_eq_zero_of_notMem_tsupport hp])
  have zr := weight_support hbox (w := fun p : ℝ × ℝ => ((p.1 * ψ p : ℝ) : ℂ))
    (fun p hp => by simp [image_eq_zero_of_notMem_tsupport hp])
  have S0 := swap_mode hvm hvl (velEvaluator_cont k 0) (velEvaluator_le k 0) hρ c0 z0.1 z0.2 η
  have S2 := swap_mode hvm hvl (velEvaluator_cont k 2) (velEvaluator_le k 2) hρ c2 z2.1 z2.2 η
  have S1 := swap_mode hvm hvl (velEvaluator_cont k 1) (velEvaluator_le k 1) hρ c1 z1.1 z1.2 η
  have S4 := swap_mode hvm hvl (velEvaluator_cont k 0) (velEvaluator_le k 0) hρ c1 z1.1 z1.2 η
  have SG := fun a : Fin 3 => swap_mode hGm hGl (gradEvaluator_cont k a a) (gradEvaluator_le k a a) hρ cr zr.1 zr.2 η
  simp only [planeVel_orbit]
  rw [S0.2.1, S2.2.1, S1.2.1, ← integral_const_mul, ← integral_add S0.2.2.1 S2.2.2.1]
  have e3 := integral_sub (S0.2.2.1.add S2.2.2.1) (S1.2.2.1.const_mul ((k : ℂ) * Complex.I))
  simp only [Pi.add_apply] at e3
  rw [← e3]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [S0.2.2.2, S2.2.2.2, S1.2.2.2, S4.2.2.2, (SG 0).2.2.2, (SG 1).2.2.2, (SG 2).2.2.2,
    ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.divergence_free] with τ i0 i2 i1 i4 g0 g1 g2 hw hdv
  have key := slice_div hw hdv k ψ hψ hc hpos (int_scale (orbit_vel k v 0 · τ) i0) (int_scale (orbit_vel k v 1 · τ) i1)
    (int_scale (orbit_vel k v 0 · τ) i4)
    (fun a => by
      fin_cases a
      · exact int_scale (orbit_grad k G 0 0 · τ) g0
      · exact int_scale (orbit_grad k G 1 1 · τ) g1
      · exact int_scale (orbit_grad k G 2 2 · τ) g2)
  simp only [Pi.zero_apply]
  rw [integral_scale (orbit_vel k v 0 · τ), integral_scale (orbit_vel k v 2 · τ),
    integral_scale (orbit_vel k v 1 · τ)]
  linear_combination (phase η τ * (1 / (2 * Real.pi) : ℂ) * (2 * Real.pi : ℂ)) * key

open Internal.PatchModeWeak in
theorem planeVel_height_weak {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ) (ψ : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * planeVel η v 2 p.1 p.2 =
      -∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * planeVelHeight η G 2 p.1 p.2 := by
  obtain ⟨ρ, R, hρ, hbox⟩ := exists_box hc hpos
  have hvm := hv.measurable_velocity
  have hvl := Coercive.Internal.PerturbationFacts.velocity_locallyIntegrable hv
  have hGm := hv.measurable_gradient
  have hGl := Coercive.Internal.PerturbationFacts.gradient_locallyIntegrable hv
  set k := η.2 with hk
  have hd : Continuous (fun p => fderiv ℝ ψ p) := hψ.continuous_fderiv (by simp)
  have c2 : Continuous (fun p : ℝ × ℝ => ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.mul (hd.clm_apply continuous_const))
  have cr : Continuous (fun p : ℝ × ℝ => ((p.1 * ψ p : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.mul hψ.continuous)
  have z2 := weight_support hbox (w := fun p : ℝ × ℝ => ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ))
    (fun p hp => by simp [fderiv_off hp])
  have zr := weight_support hbox (w := fun p : ℝ × ℝ => ((p.1 * ψ p : ℝ) : ℂ))
    (fun p hp => by simp [image_eq_zero_of_notMem_tsupport hp])
  have S2 := swap_mode hvm hvl (velEvaluator_cont k 2) (velEvaluator_le k 2) hρ c2 z2.1 z2.2 η
  have SG := swap_mode hGm hGl (gradEvaluator_cont k 2 2) (gradEvaluator_le k 2 2) hρ cr zr.1 zr.2 η
  have hsupp : ∀ p ∈ tsupport (fun p : ℝ × ℝ => p.1 * ψ p), 0 < p.1 := fun p hp =>
    hpos p (tsupport_mul_subset_right hp)
  simp only [planeVel_orbit, planeHeight_orbit]
  rw [S2.2.1, SG.2.1, ← sub_eq_zero, sub_neg_eq_add, ← integral_add S2.2.2.1 SG.2.2.1]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_of_ae hv.weak_gradient] with τ hw
  have key := (slice_weak hw k (fun p : ℝ × ℝ => p.1 * ψ p) (radial_weight_smooth hψ) hc.mul_left hsupp).2
  simp only [fderiv_radial_weight hψ] at key
  simp only [Pi.zero_apply]
  rw [integral_scale (orbit_vel k v 2 · τ), integral_scale (orbit_grad k G 2 2 · τ)]
  have e : ∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * CellCert.CellAnalysis.modeVec 1 k (v τ) p.1 p.2 2 =
      -∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * CellCert.CellAnalysis.gradMode 1 k (G τ) 2 2 p := by
    rw [← key]
    congr 1
    funext p
    push_cast
    ring
  rw [e]
  ring

end Bridge

end CertCell

end Breakdown
