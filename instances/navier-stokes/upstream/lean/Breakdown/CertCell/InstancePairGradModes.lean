import Breakdown.CertCell.InstancePairStatements
import Breakdown.CertCell.ModeShiftRotateTensor
import Breakdown.CertCell.HalfPlaneReduction
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.CoerciveGain
import Breakdown.Cert.CoerciveRotation

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

namespace Internal.GradientModes

open Coercive Coercive.ModeDerivative.Internal

theorem off_axis_ae : ∀ᵐ y : Space, (pointPlane y).1 ≠ 0 := by
  have hs : (volume : Measure Space)
      (LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) : Set Space) = 0 := by
    refine Measure.addHaar_submodule _ _ fun h => ?_
    have hmem : (EuclideanSpace.single 0 1 : Space) ∈
        LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) := by
      rw [h]; trivial
    simp at hmem
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) hs
  have h0 : (pointPlane y).1 = 0 := not_not.1 hy
  have h1 : y 0 ^ 2 + y 1 ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 h0
  have h2 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  simpa [LinearMap.mem_ker] using h2

theorem field_locallyIntegrable {m : ℕ} {S : Finset (ℤ × ℤ)} {b : ℝ → Space → Space}
    (hb : ActuatorShapeFacts m S b) : LocallyIntegrable (fun z : ℝ × Space => b z.1 z.2) volume := by
  have hn := Cert.Internal.CoerciveBordered.locallyIntegrable_of_periodic_sq (fun σ y => ‖b σ y‖)
    hb.measurable.norm (fun σ y => by simp only [hb.periodic σ y]) hb.square_finite
  exact hn.mono hb.measurable (Filter.Eventually.of_forall fun z => by simp)

theorem gradient_locallyIntegrable {m : ℕ} {S : Finset (ℤ × ℤ)} {b : ℝ → Space → Space}
    (hb : ActuatorShapeFacts m S b) :
    LocallyIntegrable (fun z : ℝ × Space => gradField b z.1 z.2) volume := by
  have hcol : ∀ i, LocallyIntegrable (fun z : ℝ × Space => ‖gradField b z.1 z.2 (unitVector i)‖) volume :=
    fun i => Cert.Internal.CoerciveBordered.column_locallyIntegrable hb.gradient_measurable
      hb.gradient_periodic hb.gradient_finite i
  have hs := locallyIntegrable_finsetSum Finset.univ fun i _ => hcol i
  refine hs.mono hb.gradient_measurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  exact Coercive.Internal.PerturbationFacts.opNorm_le_sum_apply _

theorem mode_weak_gradient (hRot : AxialRotationHolds) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hvl : LocallyIntegrable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hw : ∀ s, IsWeakGradient (v s) (G s)) (ι : ℤ × ℤ) (σ : ℝ) :
    IsWeakGradient (fun y => reVec (modeVel ι v σ y)) (fun y => reMat (modeGrad ι G σ y)) ∧
      IsWeakGradient (fun y => imVec (modeVel ι v σ y)) (fun y => imMat (modeGrad ι G σ y)) := by
  have hav : ∀ K : Set Space, IsCompact K → Integrable (fun q : Space × (ℝ × ℝ) => velFamily v σ q.2 q.1)
      ((volume.restrict K).prod angleMeasure) := fun K hK =>
    integrable_of_rot (integrable_rotated hRot hvm hvl σ hK) (fun φ w => axialRot (-φ) w)
      (continuous_axialRot_comp (X := ℝ × Space) continuous_fst.neg continuous_snd)
      (fun _ _ => (norm_axialRot hRot _ _).le)
  have hag : ∀ K : Set Space, IsCompact K →
      Integrable (fun q : Space × (ℝ × ℝ) => gradFamily hRot G σ q.2 q.1)
        ((volume.restrict K).prod angleMeasure) := fun K hK =>
    integrable_of_rot (integrable_rotated hRot hGm hGl σ hK) (fun φ A => rotConj hRot φ A)
      (continuous_rotConj hRot) (fun φ A => norm_rotConj_le hRot φ A)
  have hwf : ∀ᵐ p ∂angleMeasure, IsWeakGradient (velFamily v σ p) (gradFamily hRot G σ p) := by
    refine Filter.Eventually.of_forall fun p => ?_
    refine weakGradient_rotate (hw (σ + p.1)) (rotIso hRot p.2) (fun y => ?_) (fun y u => ?_)
    · simp only [velFamily, rotIso_symm_apply, rotIso_apply]
    · simp only [gradFamily, rotConj_apply, rotIso_symm_apply, rotIso_apply]
  have sv := ae_slice_integrable hav
  have sg := ae_slice_integrable hag
  constructor
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightRe ι) (measurable_weightRe ι) (abs_weightRe_le ι) hav hag hwf) ?_ ?_
    · filter_upwards [sv] with y hy
      exact (reVec_modeAverage ι (f := fun τ φ => velFamily v σ (τ, φ) y) hy).symm
    · filter_upwards [sg] with y hy
      rw [modeGrad_eq_average hRot]
      exact (reMat_modeAverage ι (M := fun τ φ => gradFamily hRot G σ (τ, φ) y) hy).symm
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightIm ι) (measurable_weightIm ι) (abs_weightIm_le ι) hav hag hwf) ?_ ?_
    · filter_upwards [sv] with y hy
      exact (imVec_modeAverage ι (f := fun τ φ => velFamily v σ (τ, φ) y) hy).symm
    · filter_upwards [sg] with y hy
      rw [modeGrad_eq_average hRot]
      exact (imMat_modeAverage ι (M := fun τ φ => gradFamily hRot G σ (τ, φ) y) hy).symm

theorem gradient_ae_zero {f : Space → Space} {F : Space → (Space →L[ℝ] Space)} (h : IsWeakGradient f F)
    (hf : ∀ᵐ y, f y = 0) : ∀ᵐ y, F y = 0 := by
  have hcol : ∀ j : Fin 3, ∀ᵐ y, F y (unitVector j) = 0 := by
    intro j
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (Coercive.GainInternal.li_apply h.2.1 j)
      fun φ hφ hφc => ?_
    rw [h.2.2 φ ⟨hφ, hφc⟩ j, neg_eq_zero]
    have e : (fun y => fderiv ℝ φ y (unitVector j) • f y) =ᵐ[volume] fun _ => (0 : Space) := by
      filter_upwards [hf] with y hy
      rw [hy, smul_zero]
    rw [integral_congr_ae e, integral_zero]
  filter_upwards [ae_all_iff.2 hcol] with y hy
  exact clm_ext_unitVector fun j => by rw [hy j, zero_apply]

theorem entries_zero {g : Fin 3 × Fin 3 → ℂ} (hr : reMat g = 0) (hi : imMat g = 0) : g = 0 := by
  funext ij
  have a := Coercive.GainInternal.reMat_apply g ij.1 ij.2
  have c := Coercive.GainInternal.imMat_apply g ij.1 ij.2
  rw [hr] at a
  rw [hi] at c
  simp only [zero_apply, PiLp.zero_apply] at a c
  exact Complex.ext a.symm c.symm

theorem column_integrableOn (hRot : AxialRotationHolds) {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume) (σ : ℝ) :
    ∀ᵐ y : Space, ∀ j : Fin 3, IntegrableOn
      (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  have hF : ∀ K : Set Space, IsCompact K →
      Integrable (fun q : Space × (ℝ × ℝ) => G (σ + q.2.1) (axialRot q.2.2 q.1))
        ((volume.restrict K).prod angleMeasure) := fun K hK => integrable_rotated hRot hGm hGl σ hK
  have hs := ae_slice_integrable (F := fun p y => G (σ + p.1) (axialRot p.2 y)) hF
  filter_upwards [hs] with y hy j
  have hc : Continuous (fun x : (ℝ × ℝ) × (Space →L[ℝ] Space) => x.2 (axialRot x.1.2 (unitVector j))) :=
    continuous_snd.clm_apply (continuous_axialRot_comp continuous_fst.snd continuous_const)
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j))) angleMeasure :=
    (hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hy.aestronglyMeasurable) : _)
  have hcol : Integrable
      (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j))) angleMeasure := by
    refine Integrable.mono' hy.norm hm (Filter.Eventually.of_forall fun p => ?_)
    calc ‖G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j))‖
        ≤ ‖G (σ + p.1) (axialRot p.2 y)‖ * ‖axialRot p.2 (unitVector j)‖ := (G _ _).le_opNorm _
      _ = ‖G (σ + p.1) (axialRot p.2 y)‖ := by rw [norm_axialRot hRot, norm_unitVector_one, mul_one]
  have e : angleMeasure = (volume : Measure (ℝ × ℝ)).restrict
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_restrict _ _
  have h2 : IntegrableOn (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j)))
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [IntegrableOn, ← e]
    exact hcol
  refine h2.congr_set_ae ?_
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc.symm Ioc_ae_eq_Icc.symm

theorem rotated_zero {G : ℝ → Space → (Space →L[ℝ] Space)} (hG : IsTimePeriodic G) (ι : ℤ × ℤ)
    {y : Space} (hy : ∀ j : Fin 3, IntegrableOn
      (fun p : ℝ × ℝ => G (0 + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)))
    (h0 : modeGrad ι G 0 y = 0) (φ : ℝ) : modeGrad ι G 0 (axialRot φ y) = 0 := by
  have e := Bridge.modeShiftRotateTensor.1 G hG ι 0 0 φ y hy
  rw [add_zero] at e
  rw [e, h0]
  funext ij
  simp

end Internal.GradientModes

open Internal.GradientModes in
theorem actuatorGradientModes : ActuatorGradientModes := by
  intro m S b _ hb ξ hξ
  have hRot := Coercive.axialRotationHolds_proof
  have hGl := gradient_locallyIntegrable hb
  have hvz : ∀ᵐ y : Space, modeVel ξ b 0 y = 0 := by
    filter_upwards [off_axis_ae] with y hy
    by_contra hne
    obtain ⟨ι, hι, h⟩ := hb.modes_in ξ 0 y hy hne
    rcases h with h | h
    · exact (hξ ι hι).1 h
    · exact (hξ ι hι).2 h
  have hw := mode_weak_gradient hRot hb.measurable hb.gradient_measurable (field_locallyIntegrable hb) hGl
    hb.weak_gradient ξ 0
  have hre := gradient_ae_zero hw.1 (by
    filter_upwards [hvz] with y hy
    rw [hy]
    simp [Coercive.reVec])
  have him := gradient_ae_zero hw.2 (by
    filter_upwards [hvz] with y hy
    rw [hy]
    simp [Coercive.imVec])
  have hgz : ∀ᵐ y : Space, modeGrad ξ (gradField b) 0 y = 0 := by
    filter_upwards [hre, him] with y a c
    exact entries_zero a c
  have hgood := column_integrableOn hRot hb.gradient_measurable hGl 0
  set Z : Set Space := {y | ∃ φ, modeGrad ξ (gradField b) 0 (axialRot φ y) ≠ 0} with hZdef
  have hZ : volume Z = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 (hgood.and hgz))
    obtain ⟨φ, hφ⟩ := hy
    intro hyy
    exact hφ (rotated_zero hb.gradient_periodic ξ hyy.1 hyy.2 φ)
  have hrot : ∀ φ y, y ∈ Z → axialRot φ y ∈ Z := by
    rintro φ y ⟨ψ, hψ⟩
    refine ⟨ψ - φ, ?_⟩
    rw [← hRot.2.1 (ψ - φ) φ y, sub_add_cancel]
    exact hψ
  have hp := (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).1
    (Bridge.Internal.HalfPlaneReduction.plane_null Z hZ hrot)
  filter_upwards [hp] with p hpZ hpH
  have hnot := hpZ ⟨hpH.1, trivial⟩
  by_contra hne
  exact hnot ⟨0, by rw [hRot.2.2.1]; exact hne⟩

end InstancePair

end CertCell

end Breakdown
