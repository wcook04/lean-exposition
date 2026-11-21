import Breakdown.CellReduction.PotFluxRadialCell

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace Internal.RadialFlux

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (radialVec)

theorem radialVec_sum (y : Space) : ∑ i : Fin 3, radialVec y i • unitVector i = ‖y‖⁻¹ • y := by
  ext j
  fin_cases j <;> simp [radialVec, unitVector, Fin.sum_univ_three, div_eq_inv_mul]

theorem radialVec_hasFDerivAt {y : Space} (hy : y ≠ 0) (i : Fin 3) :
    HasFDerivAt (fun x : Space => ((radialVec x i : ℝ) : ℂ))
      ((Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)).comp
        (fderiv ℝ SphericalDivInternal.radialField y)) y := by
  have h := (Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)).hasFDerivAt.comp y
    (SphericalDivInternal.radialField_diff hy).hasFDerivAt
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  simp [SphericalDivInternal.radialField_apply]

theorem ray_hasDerivAt (u : Space → ℂ) {y : Space} (hu : DifferentiableAt ℝ u y) :
    HasDerivAt (fun s : ℝ => s ^ 2 • u (s • y)) (fderiv ℝ u y y + (2 : ℝ) • u y) 1 := by
  have hl : HasDerivAt (fun s : ℝ => s • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have hu1 : HasFDerivAt u (fderiv ℝ u y) ((1 : ℝ) • y) := by
    rw [one_smul]
    exact hu.hasFDerivAt
  have h := (hasDerivAt_pow 2 (1 : ℝ)).smul (hu1.comp_hasDerivAt (1 : ℝ) hl)
  refine h.congr_deriv ?_
  simp only [one_pow, one_smul, Function.comp_apply]
  norm_num

theorem radialPart_divergence (u : Space → ℂ) {y : Space} (hy : y ≠ 0) (hu : DifferentiableAt ℝ u y) :
    ∑ i : Fin 3, fderiv ℝ (fun x => u x * (radialVec x i : ℂ)) y (unitVector i) =
      (‖y‖⁻¹ : ℝ) • deriv (fun s : ℝ => s ^ 2 • u (s • y)) 1 := by
  have hprod : ∀ i : Fin 3, fderiv ℝ (fun x => u x * (radialVec x i : ℂ)) y (unitVector i) =
      u y * ((fderiv ℝ SphericalDivInternal.radialField y (unitVector i) i : ℝ) : ℂ) +
        (radialVec y i : ℂ) * fderiv ℝ u y (unitVector i) := by
    intro i
    have h : HasFDerivAt (fun x => u x * (radialVec x i : ℂ)) _ y :=
      hu.hasFDerivAt.mul (radialVec_hasFDerivAt hy i)
    rw [h.fderiv]
    simp [smul_eq_mul]
  have hdiv := SphericalDivInternal.div_radialField hy
  unfold divergenceAt at hdiv
  have hvec : ∑ i : Fin 3, (radialVec y i : ℂ) * fderiv ℝ u y (unitVector i) = fderiv ℝ u y (‖y‖⁻¹ • y) := by
    rw [← radialVec_sum y, map_sum]
    simp [map_smul, Complex.real_smul]
  rw [(ray_hasDerivAt u hu).deriv, Finset.sum_congr rfl (fun i _ => hprod i), Finset.sum_add_distrib,
    ← Finset.mul_sum, hvec, ← Complex.ofReal_sum, hdiv, map_smul]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem invNorm_locallyIntegrable (C : ℝ) : LocallyIntegrable (fun y : Space => C * ‖y‖⁻¹) volume := by
  refine locallyIntegrable_iff.2 fun k hk => ?_
  obtain ⟨R, hR⟩ := hk.isBounded.subset_ball (0 : Space)
  have h : IntegrableOn (fun y : Space => C * ‖y‖⁻¹) (Metric.ball 0 R) volume :=
    (CellCert.GivenFields.OpenLeavesInternal.invNorm_intOn R).const_mul C
  exact h.mono_set hR

theorem radialVec_norm_le (y : Space) (i : Fin 3) : |radialVec y i| ≤ 1 := by
  unfold radialVec
  rcases eq_or_ne y 0 with h | h
  · subst h
    simp
  · have hn : 0 < ‖y‖ := norm_pos_iff.2 h
    rw [abs_div, abs_of_pos hn, div_le_one hn]
    have := PiLp.norm_apply_le y i
    rwa [Real.norm_eq_abs] at this

theorem radialPart_of (u : Space → ℂ) (hu : Measurable u) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, ‖u y‖ ≤ B)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hSlopeBound : ∀ y : Space, y ≠ 0 →
      LipschitzOnWith (Real.toNNReal C) (fun s : ℝ => s ^ 2 • u (s • y)) (Metric.ball 1 (1 / 2)))
    (hd : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 ∧ DifferentiableAt ℝ u y) :
    (∀ i : Fin 3, LocallyIntegrable (fun y => u y * (radialVec y i : ℂ))) ∧
      (∀ᵐ y, ∀ i : Fin 3, DifferentiableAt ℝ (fun x => u x * (radialVec x i : ℂ)) y) ∧
      LocallyIntegrable (fun y => ∑ i : Fin 3, fderiv ℝ (fun x => u x * (radialVec x i : ℂ)) y (unitVector i)) ∧
      ∀ φ, IsTestFunction φ →
        ∫ y, (φ y : ℂ) * (∑ i : Fin 3, fderiv ℝ (fun x => u x * (radialVec x i : ℂ)) y (unitVector i)) =
          -∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * (u y * (radialVec y i : ℂ)) := by
  set D : Space → ℂ := fun y => deriv (fun s : ℝ => s ^ 2 • u (s • y)) 1 with hDdef
  have hDhas : ∀ᵐ y ∂(volume : Measure Space), HasDerivAt (fun s : ℝ => s ^ 2 • u (s • y)) (D y) 1 := by
    filter_upwards [hd] with y hy
    exact (ray_hasDerivAt u hy.2).differentiableAt.hasDerivAt
  have hDm : AEStronglyMeasurable D volume :=
    rayDeriv_aestronglyMeasurable u hu (hDhas.mono fun y hy => hy.differentiableAt)
  have hDb : ∀ y : Space, y ≠ 0 → ‖D y‖ ≤ C := by
    intro y hy
    have h := norm_deriv_le_of_lipschitzOn (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
      (hSlopeBound y hy)
    rwa [Real.coe_toNNReal _ hC0] at h
  have hdiv : ∀ᵐ y ∂(volume : Measure Space),
      ∑ i : Fin 3, fderiv ℝ (fun x => u x * (radialVec x i : ℂ)) y (unitVector i) = (‖y‖⁻¹ : ℝ) • D y := by
    filter_upwards [hd] with y hy
    exact radialPart_divergence u hy.1 hy.2
  have hrm : ∀ i : Fin 3, Measurable (fun y : Space => ((radialVec y i : ℝ) : ℂ)) := fun i =>
    Complex.measurable_ofReal.comp
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.measurable.div measurable_norm)
  refine ⟨fun i => ?_, ?_, ?_, fun φ hφ => ?_⟩
  · refine (locallyIntegrable_const B).mono (hu.mul (hrm i)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg hB0]
    calc ‖u y‖ * |radialVec y i| ≤ B * 1 := mul_le_mul (hB y) (radialVec_norm_le y i) (abs_nonneg _) hB0
      _ = B := mul_one B
  · filter_upwards [hd] with y hy i
    exact hy.2.mul (radialVec_hasFDerivAt hy.1 i).differentiableAt
  · have hmain : LocallyIntegrable (fun y : Space => (‖y‖⁻¹ : ℝ) • D y) volume := by
      refine (invNorm_locallyIntegrable C).mono
        (measurable_norm.inv.aestronglyMeasurable.smul hDm) ?_
      filter_upwards [hd] with y hy
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg y)),
        abs_of_nonneg (mul_nonneg hC0 (inv_nonneg.2 (norm_nonneg y))), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hDb y hy.1) (inv_nonneg.2 (norm_nonneg y))
    exact hmain.congr (hdiv.mono fun y hy => hy.symm)
  · obtain ⟨-, hw⟩ := radialWeak u hu hB0 hB hC0 hSlopeBound D hDhas hDm φ hφ
    have hL : ∫ y, (φ y : ℂ) * (∑ i : Fin 3, fderiv ℝ (fun x => u x * (radialVec x i : ℂ)) y (unitVector i)) =
        ∫ y, φ y • ((‖y‖⁻¹ : ℝ) • D y) := by
      refine integral_congr_ae ?_
      filter_upwards [hdiv] with y hy
      rw [hy]
      exact Complex.real_smul.symm
    have hR : (fun y => ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) * (u y * (radialVec y i : ℂ))) =
        fun y => fderiv ℝ φ y (‖y‖⁻¹ • y) • u y := by
      funext y
      rw [← radialVec_sum y, map_sum, Complex.real_smul]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
      push_cast
      ring
    rw [hL, hR, hw, neg_neg]

end Internal.RadialFlux

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (radialVec)

open Internal.RadialFlux in
theorem radialFluxPart_divergence_ae (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P)
    (κ : FieldKey) (c : PotComponent) (σ : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space),
      ∑ i : Fin 3, fderiv ℝ (fun x => componentValue P κ (F.data κ).radialFlux c σ x * (radialVec x i : ℂ)) y
        (unitVector i) =
      (‖y‖⁻¹ : ℝ) • deriv (fun s : ℝ => s ^ 2 • componentValue P κ (F.data κ).radialFlux c σ (s • y)) 1 := by
  filter_upwards [scalarValue_ae_differentiable P hP κ (labelAzimuth P.azimuthOrder κ.label + c.shift)
    c.carriesSine ((F.data κ).radialFlux c) σ] with y hy
  exact radialPart_divergence (componentValue P κ (F.data κ).radialFlux c σ) hy.1 hy.2

open Internal.RadialFlux in
theorem radialFluxPart_weakDivergence (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P)
    (hF : IsPotentialSeries F) (κ : FieldKey) (hκ : κ ∈ F.keys) (c : PotComponent) (σ : ℝ) :
    (∀ i : Fin 3, LocallyIntegrable
      (fun y => componentValue P κ (F.data κ).radialFlux c σ y * (radialVec y i : ℂ))) ∧
    (∀ᵐ y, ∀ i : Fin 3, DifferentiableAt ℝ
      (fun x => componentValue P κ (F.data κ).radialFlux c σ x * (radialVec x i : ℂ)) y) ∧
    LocallyIntegrable (fun y => ∑ i : Fin 3, fderiv ℝ
      (fun x => componentValue P κ (F.data κ).radialFlux c σ x * (radialVec x i : ℂ)) y (unitVector i)) ∧
    ∀ φ, IsTestFunction φ →
      ∫ y, (φ y : ℂ) * (∑ i : Fin 3, fderiv ℝ
        (fun x => componentValue P κ (F.data κ).radialFlux c σ x * (radialVec x i : ℂ)) y (unitVector i)) =
      -∫ y, ∑ i : Fin 3, (fderiv ℝ φ y (unitVector i) : ℂ) *
        (componentValue P κ (F.data κ).radialFlux c σ y * (radialVec y i : ℂ)) := by
  obtain ⟨B, hB0, hB⟩ := scalarValue_bound P hP κ (labelAzimuth P.azimuthOrder κ.label + c.shift)
    c.carriesSine ((F.data κ).radialFlux c) σ
  obtain ⟨C, hC0, hC⟩ := scalarValue_raySlopeBound P hP κ (labelAzimuth P.azimuthOrder κ.label + c.shift)
    c.carriesSine ((F.data κ).radialFlux c) σ (hF.radialFlux_mesh κ hκ c).1
  exact radialPart_of (componentValue P κ (F.data κ).radialFlux c σ)
    (scalarValue_measurable P hP κ _ _ _ σ) hB0 hB hC0 hC
    (scalarValue_ae_differentiable P hP κ _ _ _ σ)

end PotentialShape

end Breakdown
