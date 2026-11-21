import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.TailAngularPlane
import Breakdown.CertCell.HarmonicLocal

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.HarmonicProfiles

open Coercive.Internal.ModeRotation (expFactor continuous_expFactor norm_expFactor)

theorem rot_add_two_pi (φ : ℝ) (y : Space) : axialRot (φ + 2 * Real.pi) y = axialRot φ y := by
  simp only [axialRot, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem norm_rot (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [axialRot, unitVector, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
    Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem cylPoint_eq_rot (θ : ℝ) (p : ℝ × ℝ) :
    CellCert.CellAnalysis.cylPoint p.1 θ p.2 = axialRot θ (planePoint p) := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, unitVector] <;> ring

theorem frameUnit_add_two_pi (φ : ℝ) (a : Fin 3) : frameUnit (φ + 2 * Real.pi) a = frameUnit φ a := by
  simp only [frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem norm_frameUnit (φ : ℝ) (a : Fin 3) : ‖frameUnit φ a‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  fin_cases a <;> simp [frameUnit, radialUnit, angularUnit, axialUnit, Fin.sum_univ_three,
    PiLp.single_apply]

theorem single_eq_smul (i : Fin 3) (x : ℝ) : EuclideanSpace.single i x = x • unitVector i := by
  ext j
  by_cases h : j = i <;> simp [unitVector, PiLp.single_apply, h]

theorem continuous_frameUnit (a : Fin 3) : Continuous (fun φ => frameUnit φ a) := by
  fin_cases a <;> simp only [frameUnit, radialUnit, angularUnit, axialUnit, single_eq_smul] <;> fun_prop

theorem rot_neg_apply (φ : ℝ) (x : Space) (a : Fin 3) :
    axialRot (-φ) x a = inner ℝ (frameUnit φ a) x := by
  fin_cases a <;> simp [axialRot, frameUnit, radialUnit, angularUnit, axialUnit, unitVector,
    PiLp.inner_apply, Fin.sum_univ_three, PiLp.single_apply] <;> ring

theorem rot_unitVector (φ : ℝ) (b : Fin 3) : axialRot φ (unitVector b) = frameUnit φ b := by
  ext i
  fin_cases b <;> fin_cases i <;> simp [axialRot, frameUnit, radialUnit, angularUnit, axialUnit, unitVector,
    PiLp.single_apply]

theorem frameVec_eq (θ : ℝ) (u : Space) (a : Fin 3) : frameVec θ u a = inner ℝ (frameUnit θ a) u := by
  fin_cases a <;> simp [frameVec, frameUnit, real_inner_comm]

theorem frameMat_eq (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat θ M a b = inner ℝ (frameUnit θ a) (M (frameUnit θ b)) := by
  simp only [frameMat, frameUnit]
  exact real_inner_comm _ _

theorem frameThird_eq (θ : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird θ H a b c = inner ℝ (frameUnit θ a) (H (frameUnit θ c) (frameUnit θ b)) := by
  simp only [frameThird]
  exact real_inner_comm _ _

theorem exp_angle_add_two_pi (k : ℤ) (θ : ℝ) :
    Complex.exp (-(((k : ℝ) * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  have e : -(((k : ℝ) * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I
      = -(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem expFactor_eq (ν k : ℤ) (τ θ : ℝ) :
    expFactor (ν, k) τ θ = Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)
      * ((Real.cos (2 * Real.pi * ν * τ) : ℂ) + Complex.I * (-(Real.sin (2 * Real.pi * ν * τ)) : ℂ)) := by
  have e : expFactor (ν, k) τ θ = Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((-(2 * Real.pi * ν * τ) : ℝ) : ℂ) * Complex.I) := by
    unfold expFactor
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e, Complex.exp_mul_I (((-(2 * Real.pi * ν * τ)) : ℝ) : ℂ), ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem expFactor_add_two_pi (ν k : ℤ) (τ θ : ℝ) :
    expFactor (ν, k) τ (θ + 2 * Real.pi) = expFactor (ν, k) τ θ := by
  rw [expFactor_eq, expFactor_eq, exp_angle_add_two_pi]

end Internal.HarmonicProfiles

namespace Internal.HarmonicProfiles

open Coercive.Internal.ModeRotation (expFactor continuous_expFactor norm_expFactor)

theorem norm_exp_angle (k : ℤ) (θ : ℝ) : ‖Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem integrable_weighted (f : ℝ × ℝ → X) {μ : Measure (ℝ × ℝ)} (hf : Integrable f μ) (Φ : ℝ → X →L[ℝ] ℝ)
    (hΦc : Continuous Φ) (hΦb : ∀ φ x, ‖Φ φ x‖ ≤ ‖x‖) (K : ℝ × ℝ → ℂ) (hKc : Continuous K)
    (hKb : ∀ q, ‖K q‖ ≤ 1) :
    Integrable (fun q => K q * ((Φ q.2 (f q) : ℝ) : ℂ)) μ := by
  refine hf.norm.mono' ?_ (Eventually.of_forall fun q => ?_)
  · have hc : Continuous (fun w : (ℝ × ℝ) × X => K w.1 * ((Φ w.1.2 w.2 : ℝ) : ℂ)) :=
      (hKc.comp continuous_fst).mul (Complex.continuous_ofReal.comp
        ((hΦc.comp (continuous_snd.comp continuous_fst)).clm_apply continuous_snd))
    exact hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hf.aestronglyMeasurable)
  · rw [norm_mul, Complex.norm_real]
    calc ‖K q‖ * ‖Φ q.2 (f q)‖ ≤ 1 * ‖f q‖ :=
          mul_le_mul (hKb q) (hΦb q.2 (f q)) (norm_nonneg _) zero_le_one
      _ = ‖f q‖ := one_mul _

theorem slice_eval (f : ℝ × ℝ → X) (Φ : ℝ → X →L[ℝ] ℝ) (θ : ℝ) (c : ℝ → ℝ) (hc : Continuous c)
    (hθ : Integrable (fun τ => f (τ, θ)) (volume.restrict (Set.Ioc (0 : ℝ) 1))) (w : ℂ) :
    w * ((Φ θ (∫ τ in Set.Icc (0 : ℝ) 1, c τ • f (τ, θ)) : ℝ) : ℂ)
      = ∫ τ in Set.Ioc (0 : ℝ) 1, w * ((c τ : ℝ) : ℂ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ) := by
  have hi : Integrable (fun τ => c τ • f (τ, θ)) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    IntegrableOn.continuousOn_smul (by rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact hθ) hc.continuousOn isCompact_Icc
  rw [← ContinuousLinearMap.integral_comp_comm _ hi]
  simp only [map_smul, smul_eq_mul]
  rw [← integral_complex_ofReal, ← integral_const_mul, ← setIntegral_congr_set Ioc_ae_eq_Icc]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  push_cast
  ring

theorem period_shift (g : ℝ → ℂ) (hg : Function.Periodic g (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ = ∫ θ in Set.Ioc (-Real.pi) Real.pi, g θ := by
  have h := hg.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

theorem mode_split (f : ℝ × ℝ → X)
    (hf : Integrable f ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (-Real.pi) Real.pi))))
    (hper : ∀ τ θ, f (τ, θ + 2 * Real.pi) = f (τ, θ)) (Φ : ℝ → X →L[ℝ] ℝ) (hΦc : Continuous Φ)
    (hΦb : ∀ φ x, ‖Φ φ x‖ ≤ ‖x‖) (hΦp : ∀ φ, Φ (φ + 2 * Real.pi) = Φ φ) (ν k : ℤ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        expFactor (ν, k) τ φ * ((Φ φ (f (τ, φ)) : ℝ) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
            ((Φ θ (∫ τ in Set.Icc (0 : ℝ) 1, Real.cos (2 * Real.pi * ν * τ) • f (τ, θ)) : ℝ) : ℂ))
        + Complex.I * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
            ((Φ θ (-∫ τ in Set.Icc (0 : ℝ) 1, Real.sin (2 * Real.pi * ν * τ) • f (τ, θ)) : ℝ) : ℂ)) := by
  set KA : ℝ × ℝ → ℂ := fun q => Complex.exp (-(((k : ℝ) * q.2 : ℝ) : ℂ) * Complex.I) *
    ((Real.cos (2 * Real.pi * ν * q.1) : ℝ) : ℂ) with hKA
  set KB : ℝ × ℝ → ℂ := fun q => Complex.exp (-(((k : ℝ) * q.2 : ℝ) : ℂ) * Complex.I) *
    ((-Real.sin (2 * Real.pi * ν * q.1) : ℝ) : ℂ) with hKB
  have iA := integrable_weighted f hf Φ hΦc hΦb KA (by rw [hKA]; fun_prop) (fun q => by
    rw [hKA, norm_mul, norm_exp_angle, Complex.norm_real, one_mul, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _)
  have iB := integrable_weighted f hf Φ hΦc hΦb KB (by rw [hKB]; fun_prop) (fun q => by
    rw [hKB, norm_mul, norm_exp_angle, Complex.norm_real, one_mul, Real.norm_eq_abs, abs_neg]
    exact Real.abs_sin_le_one _)
  have iG := integrable_weighted f hf Φ hΦc hΦb (fun q => expFactor (ν, k) q.1 q.2)
    ((continuous_expFactor (ν, k))) (fun q => (norm_expFactor _ _ _).le)
  have hsplit : ∀ q : ℝ × ℝ, expFactor (ν, k) q.1 q.2 * ((Φ q.2 (f q) : ℝ) : ℂ)
      = KA q * ((Φ q.2 (f q) : ℝ) : ℂ) + Complex.I * (KB q * ((Φ q.2 (f q) : ℝ) : ℂ)) := by
    intro q
    rw [expFactor_eq, hKA, hKB]
    push_cast
    ring
  have hL : ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor (ν, k) τ φ * ((Φ φ (f (τ, φ)) : ℝ) : ℂ)
      = ∫ θ in Set.Ioc (-Real.pi) Real.pi, ∫ τ in Set.Ioc (0 : ℝ) 1,
          (KA (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ) + Complex.I * (KB (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ))) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    have h1 : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor (ν, k) τ φ * ((Φ φ (f (τ, φ)) : ℝ) : ℂ)
        = ∫ φ in Set.Ioc (-Real.pi) Real.pi, expFactor (ν, k) τ φ * ((Φ φ (f (τ, φ)) : ℝ) : ℂ) := by
      intro τ
      refine period_shift _ fun φ => ?_
      simp only [expFactor_add_two_pi, hΦp, hper]
    simp_rw [h1]
    rw [integral_integral_swap iG]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    exact hsplit (τ, θ)
  have hA : ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
        ((Φ θ (∫ τ in Set.Icc (0 : ℝ) 1, Real.cos (2 * Real.pi * ν * τ) • f (τ, θ)) : ℝ) : ℂ)
      = ∫ θ in Set.Ioc (-Real.pi) Real.pi, ∫ τ in Set.Ioc (0 : ℝ) 1, KA (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ) := by
    rw [period_shift _ fun θ => by simp only [exp_angle_add_two_pi, hΦp, hper]]
    refine integral_congr_ae ?_
    filter_upwards [hf.prod_left_ae] with θ hθ
    rw [slice_eval f Φ θ _ (by fun_prop) hθ]
  have hneg : ∀ θ, -∫ τ in Set.Icc (0 : ℝ) 1, Real.sin (2 * Real.pi * ν * τ) • f (τ, θ)
      = ∫ τ in Set.Icc (0 : ℝ) 1, (-Real.sin (2 * Real.pi * ν * τ)) • f (τ, θ) := by
    intro θ
    rw [← integral_neg]
    simp only [neg_smul]
  have hB : ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
        ((Φ θ (-∫ τ in Set.Icc (0 : ℝ) 1, Real.sin (2 * Real.pi * ν * τ) • f (τ, θ)) : ℝ) : ℂ)
      = ∫ θ in Set.Ioc (-Real.pi) Real.pi, ∫ τ in Set.Ioc (0 : ℝ) 1, KB (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ) := by
    simp_rw [hneg]
    rw [period_shift _ fun θ => by simp only [exp_angle_add_two_pi, hΦp, hper]]
    refine integral_congr_ae ?_
    filter_upwards [hf.prod_left_ae] with θ hθ
    rw [slice_eval f Φ θ _ (by fun_prop) hθ]
  have e : ∫ θ in Set.Ioc (-Real.pi) Real.pi, ∫ τ in Set.Ioc (0 : ℝ) 1,
        (KA (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ) + Complex.I * (KB (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ)))
      = (∫ θ in Set.Ioc (-Real.pi) Real.pi, ∫ τ in Set.Ioc (0 : ℝ) 1, KA (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ))
        + Complex.I * ∫ θ in Set.Ioc (-Real.pi) Real.pi, ∫ τ in Set.Ioc (0 : ℝ) 1,
          KB (τ, θ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ) := by
    rw [← integral_const_mul (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) Complex.I,
      ← integral_add iA.integral_prod_right (iB.integral_prod_right.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [iA.prod_left_ae, iB.prod_left_ae] with θ h1 h2
    rw [integral_add h1 (h2.const_mul _), integral_const_mul]
  rw [hL, hA, hB, e]
  ring

end Internal.HarmonicProfiles

namespace Internal.HarmonicProfiles

theorem continuous_orbitTime :
    Continuous (fun x : (ℝ × (ℝ × ℝ)) × ℝ => ((x.1.1, axialRot x.2 (planePoint x.1.2)) : ℝ × Space)) := by
  have e : (fun x : (ℝ × (ℝ × ℝ)) × ℝ => ((x.1.1, axialRot x.2 (planePoint x.1.2)) : ℝ × Space))
      = fun x => (x.1.1, axialRot x.2 (x.1.2.1 • unitVector 0 + x.1.2.2 • unitVector 2)) := by
    funext x
    rw [TailBand.Internal.AngularPlane.planePoint_eq]
  rw [e]
  unfold axialRot
  fun_prop

theorem lintegral_cyl_time (W : ℝ × Space → ℝ≥0∞) (hW : Measurable W) (T : Set ℝ) :
    ∫⁻ τ in T, ∫⁻ y, W (τ, y) = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.univ, ENNReal.ofReal p.1 *
      ∫⁻ τ in T, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, W (τ, axialRot θ (planePoint p)) := by
  have hm : Measurable (fun x : (ℝ × (ℝ × ℝ)) × ℝ => W (x.1.1, axialRot x.2 (planePoint x.1.2))) :=
    hW.comp continuous_orbitTime.measurable
  have hI : Measurable (fun x : ℝ × (ℝ × ℝ) =>
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, W (x.1, axialRot θ (planePoint x.2))) := hm.lintegral_prod_right'
  calc ∫⁻ τ in T, ∫⁻ y, W (τ, y)
      = ∫⁻ τ in T, ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.univ, ENNReal.ofReal p.1 *
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, W (τ, axialRot θ (planePoint p)) := by
        refine lintegral_congr fun τ => ?_
        exact TailBand.lintegral_eq_cylindrical (fun y => W (τ, y)) (hW.comp measurable_prodMk_left)
    _ = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.univ, ∫⁻ τ in T, ENNReal.ofReal p.1 *
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, W (τ, axialRot θ (planePoint p)) :=
        lintegral_lintegral_swap
          (((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul hI).aemeasurable)
    _ = _ := by
        refine lintegral_congr fun p => ?_
        exact lintegral_const_mul _ (hI.comp (measurable_id.prodMk measurable_const))

theorem ae_integrable_orbit {X : Type*} [NormedAddCommGroup X] (u : ℝ × Space → X)
    (hu : AEStronglyMeasurable u volume)
    (hloc : ∀ R : ℝ, ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖u z‖ₑ < ⊤) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
      Integrable (fun q : ℝ × ℝ => u (q.1, axialRot q.2 (planePoint p)))
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) := by
  set u' := hu.mk u with hu'def
  have hu' : StronglyMeasurable u' := hu.stronglyMeasurable_mk
  have hae : u =ᵐ[volume] u' := hu.ae_eq_mk
  set N := toMeasurable volume {z | u z ≠ u' z} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact hae
  have hsub : {z | u z ≠ u' z} ⊆ N := subset_toMeasurable _ _
  have hS : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hrestr : (volume.restrict (Set.Ioo (-Real.pi) Real.pi) : Measure ℝ)
      = volume.restrict (Set.Ioc (-Real.pi) Real.pi) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hmN : Measurable (N.indicator (1 : ℝ × Space → ℝ≥0∞)) := measurable_one.indicator hNm
  have hnull : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
      ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        N.indicator (1 : ℝ × Space → ℝ≥0∞) (τ, axialRot θ (planePoint p)) = 0 := by
    have h0 : ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y, N.indicator (1 : ℝ × Space → ℝ≥0∞) (τ, y) = 0 := by
      refine le_antisymm ?_ zero_le
      calc ∫⁻ τ in Set.Ioc (0 : ℝ) 1, ∫⁻ y, N.indicator (1 : ℝ × Space → ℝ≥0∞) (τ, y)
          ≤ ∫⁻ τ, ∫⁻ y, N.indicator (1 : ℝ × Space → ℝ≥0∞) (τ, y) := setLIntegral_le_lintegral _ _
        _ = ∫⁻ z, N.indicator (1 : ℝ × Space → ℝ≥0∞) z := by
            rw [Measure.volume_eq_prod, lintegral_prod _ hmN.aemeasurable]
        _ = 0 := by rw [lintegral_indicator_one hNm, hN0]
    rw [lintegral_cyl_time _ hmN] at h0
    have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ∫⁻ τ in Set.Ioc (0 : ℝ) 1,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, N.indicator (1 : ℝ × Space → ℝ≥0∞) (τ, axialRot θ (planePoint p))) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
      exact ((hmN.comp continuous_orbitTime.measurable).lintegral_prod_right').lintegral_prod_left'
    have h1 := (lintegral_eq_zero_iff hmeas).1 h0
    rw [Filter.EventuallyEq, ae_restrict_iff' hS] at h1
    filter_upwards [h1] with p hp hp0
    have h2 := hp ⟨hp0, Set.mem_univ _⟩
    simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero] at h2
    rcases h2 with h | h
    · linarith
    · exact h
  have hfin : ∀ R : ℕ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
      ∫⁻ τ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R).indicator (fun z => ‖u' z‖ₑ)
          (τ, axialRot θ (planePoint p)) < ⊤ := by
    intro R
    have hBm : MeasurableSet (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
      measurableSet_Ioc.prod Metric.isClosed_closedBall.measurableSet
    have hmW : Measurable ((Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R).indicator
        (fun z => ‖u' z‖ₑ)) :=
      (continuous_enorm.comp_stronglyMeasurable hu').measurable.indicator hBm
    have h0 : ∫⁻ τ in Set.univ, ∫⁻ y, (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R).indicator
        (fun z => ‖u' z‖ₑ) (τ, y) < ⊤ := by
      rw [Measure.restrict_univ, ← lintegral_prod _ hmW.aemeasurable, ← Measure.volume_eq_prod,
        lintegral_indicator hBm]
      calc ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖u' z‖ₑ
          = ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖u z‖ₑ :=
            lintegral_congr_ae (ae_restrict_of_ae (hae.mono fun z hz => by simp only [hz]))
        _ < ⊤ := hloc R
    rw [lintegral_cyl_time _ hmW] at h0
    have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ∫⁻ τ in Set.univ,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R).indicator
          (fun z => ‖u' z‖ₑ) (τ, axialRot θ (planePoint p))) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
      exact ((hmW.comp continuous_orbitTime.measurable).lintegral_prod_right').lintegral_prod_left'
    have h1 := ae_lt_top' hmeas.aemeasurable h0.ne
    rw [ae_restrict_iff' hS] at h1
    filter_upwards [h1] with p hp hp0
    have h2 := hp ⟨hp0, Set.mem_univ _⟩
    rw [Measure.restrict_univ] at h2
    exact ENNReal.lt_top_of_mul_ne_top_right h2.ne (by rw [Ne, ENNReal.ofReal_eq_zero]; linarith)
  filter_upwards [hnull, ae_all_iff.2 hfin] with p hpn hpf hp0
  obtain ⟨R, hR⟩ := exists_nat_ge ‖planePoint p‖
  have hcq : Continuous (fun q : ℝ × ℝ => ((q.1, axialRot q.2 (planePoint p)) : ℝ × Space)) :=
    continuous_orbitTime.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => ((q.1, p), q.2)))
  have hf'm : StronglyMeasurable (fun q : ℝ × ℝ => u' (q.1, axialRot q.2 (planePoint p))) :=
    hu'.comp_measurable hcq.measurable
  have heq : (fun q : ℝ × ℝ => u (q.1, axialRot q.2 (planePoint p)))
      =ᵐ[(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (-Real.pi) Real.pi))]
        (fun q : ℝ × ℝ => u' (q.1, axialRot q.2 (planePoint p))) := by
    rw [← hrestr]
    have hm2 : Measurable (fun q : ℝ × ℝ => N.indicator (1 : ℝ × Space → ℝ≥0∞) (q.1, axialRot q.2 (planePoint p))) :=
      hmN.comp hcq.measurable
    have h3 : ∫⁻ q, N.indicator (1 : ℝ × Space → ℝ≥0∞) (q.1, axialRot q.2 (planePoint p))
        ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) = 0 := by
      rw [lintegral_prod _ hm2.aemeasurable]
      exact hpn hp0
    filter_upwards [(lintegral_eq_zero_iff hm2).1 h3] with q hq
    by_contra hne
    have hmem : (q.1, axialRot q.2 (planePoint p)) ∈ N := hsub hne
    simp [Set.indicator_of_mem hmem] at hq
  have hfinq : ∫⁻ q, ‖u' (q.1, axialRot q.2 (planePoint p))‖ₑ
      ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) < ⊤ := by
    rw [← hrestr, lintegral_prod _ (continuous_enorm.comp_stronglyMeasurable hf'm).measurable.aemeasurable]
    refine lt_of_le_of_lt ?_ (hpf R hp0)
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_mono fun τ => ?_
    by_cases hτ : τ ∈ Set.Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hτ]
      refine le_of_eq (lintegral_congr fun θ => ?_)
      have hmem : (τ, axialRot θ (planePoint p)) ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R :=
        ⟨hτ, by rw [Metric.mem_closedBall, dist_zero_right, norm_rot]; exact hR⟩
      rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hτ]
      exact zero_le
  exact Integrable.congr ⟨hf'm.aestronglyMeasurable, hfinq⟩ heq.symm

end Internal.HarmonicProfiles

namespace Internal.HarmonicProfiles

theorem prod_restrict_univ (s : Set ℝ) :
    (volume.restrict s).prod (volume : Measure Space) = (volume : Measure (ℝ × Space)).restrict (s ×ˢ Set.univ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem setLIntegral_le_period (w : ℝ × Space → ℝ≥0∞) (hw : AEMeasurable w volume) (R : ℝ) :
    ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, w z
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, w (σ, y) := by
  calc ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, w z
      ≤ ∫⁻ z in Set.Icc (0 : ℝ) 1 ×ˢ Set.univ, w z :=
        lintegral_mono_set (Set.prod_mono Set.Ioc_subset_Icc_self (Set.subset_univ _))
    _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, w (σ, y) := by
        rw [← prod_restrict_univ, lintegral_prod _ (by rw [prod_restrict_univ]; exact hw.restrict)]

theorem volume_box_lt_top (R : ℝ) :
    volume (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) < ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_closedBall_lt_top

theorem opNorm_le_sum {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : Space →L[ℝ] Y) :
    ‖L‖ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun x => ?_
  have hx : x = ∑ i : Fin 3, x i • unitVector i := by
    ext j
    fin_cases j <;> simp [unitVector, Fin.sum_univ_three, PiLp.single_apply]
  calc ‖L x‖ = ‖∑ i : Fin 3, x i • L (unitVector i)‖ := by
        conv_lhs => rw [hx]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖x i • L (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ * ‖x‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖L (unitVector i)‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm

theorem sum_le_one_add (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) : ∑ i, a i ≤ 1 + 3 * ∑ i, a i ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  push_cast at h1
  have h0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  nlinarith [sq_nonneg (∑ i, a i - 1)]

theorem norm_le_one_add_columnSquares (M : Space →L[ℝ] Space) : ‖M‖ ≤ 1 + 3 * matSq M :=
  (opNorm_le_sum M).trans (sum_le_one_add _ fun _ => norm_nonneg _)

theorem norm_le_second (M : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖M‖ ≤ 1 + 9 * ∑ i : Fin 3, ∑ j : Fin 3, ‖M (unitVector i) (unitVector j)‖ ^ 2 := by
  have h1 := (opNorm_le_sum M).trans (sum_le_one_add _ fun _ => norm_nonneg _)
  have h2 : ∀ i, ‖M (unitVector i)‖ ^ 2 ≤ 3 * ∑ j : Fin 3, ‖M (unitVector i) (unitVector j)‖ ^ 2 := by
    intro i
    have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖M (unitVector i) (unitVector j)‖)
    rw [Finset.card_univ, Fintype.card_fin] at h3
    push_cast at h3
    have h4 := opNorm_le_sum (M (unitVector i))
    have h5 : 0 ≤ ‖M (unitVector i)‖ := norm_nonneg _
    nlinarith
  have h6 : ∑ i : Fin 3, ‖M (unitVector i)‖ ^ 2 ≤ ∑ i : Fin 3, 3 * ∑ j : Fin 3, ‖M (unitVector i) (unitVector j)‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => h2 i
  rw [← Finset.mul_sum] at h6
  linarith

theorem columnSquares_nonneg (M : Space →L[ℝ] Space) : 0 ≤ matSq M := by
  unfold matSq
  positivity

theorem enorm_le_ofReal {Y : Type*} [NormedAddCommGroup Y] (y : Y) (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : ‖y‖ ≤ 1 + c * s) : ‖y‖ₑ ≤ 1 + ENNReal.ofReal c * ENNReal.ofReal s := by
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (mul_nonneg hc hs)]
  exact ENNReal.ofReal_le_ofReal h

theorem lintegral_box_lt_top {Y : Type*} [NormedAddCommGroup Y] (u : ℝ × Space → Y) (s : ℝ × Space → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hs : ∀ z, 0 ≤ s z) (hb : ∀ z, ‖u z‖ ≤ 1 + c * s z) (hsm : AEMeasurable s volume)
    (hfin : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (s (σ, y)) < ⊤) (R : ℝ) :
    ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖u z‖ₑ < ⊤ := by
  calc ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖u z‖ₑ
      ≤ ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R,
          (1 + ENNReal.ofReal c * ENNReal.ofReal (s z)) :=
        lintegral_mono fun z => enorm_le_ofReal _ c _ hc (hs z) (hb z)
    _ = volume (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) +
          ENNReal.ofReal c * ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ENNReal.ofReal (s z) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨volume_box_lt_top R, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
        exact lt_of_le_of_lt (setLIntegral_le_period _ (ENNReal.measurable_ofReal.comp_aemeasurable hsm) R) hfin

end Internal.HarmonicProfiles

namespace Internal.HarmonicProfiles

theorem box_velocity (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H) (R : ℝ) :
    ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖v z.1 z.2‖ₑ < ⊤ := by
  set C : ℝ≥0∞ := volume (Metric.closedBall (0 : Space) R) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)
    with hCdef
  have hC : C ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg ?_ measure_closedBall_lt_top.ne).ne
    norm_num
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    rw [prod_restrict_univ]
    exact hv.measurable_velocity.restrict
  have hsl := hm.prodMk_left
  have hbound : ∀ᵐ σ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ∫⁻ y in Metric.closedBall (0 : Space) R, ‖v σ y‖ₑ
        ≤ C * (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ ((1 : ℝ) / 6) := by
    filter_upwards [hsl] with σ hσ
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 6) (by norm_num)
      (hσ.restrict (s := Metric.closedBall (0 : Space) R))
    rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h1
    refine h1.trans ?_
    rw [mul_comm]
    gcongr C * ?_
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (le_of_eq ?_)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have e6 : (6 : ℝ≥0∞).toReal = 6 := by norm_num
    rw [e6]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_cast
  calc ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖v z.1 z.2‖ₑ
      = ∫⁻ σ in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ‖v σ y‖ₑ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact hv.measurable_velocity.enorm.restrict
    _ ≤ ∫⁻ σ in Set.Ioc (0 : ℝ) 1, C * (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ ((1 : ℝ) / 6) :=
        lintegral_mono_ae hbound
    _ = C * ∫⁻ σ in Set.Ioc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ ((1 : ℝ) / 6) :=
        lintegral_const_mul' _ _ hC
    _ ≤ C * ∫⁻ σ in Set.Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ ((1 : ℝ) / 6) :=
        by gcongr C * ?_; exact lintegral_mono_set Set.Ioc_subset_Icc_self
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top hv.sixth_power_integrated

theorem box_gradient (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H) (R : ℝ) :
    ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖G z.1 z.2‖ₑ < ⊤ := by
  have hc : Continuous (fun M : Space →L[ℝ] Space => matSq M) := by
    unfold matSq
    fun_prop
  exact lintegral_box_lt_top (fun z => G z.1 z.2) (fun z => matSq (G z.1 z.2)) 3 (by norm_num)
    (fun z => columnSquares_nonneg _) (fun z => norm_le_one_add_columnSquares _)
    (hc.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable hv.gradient_finite R

theorem box_secondDeriv (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H) (R : ℝ) :
    ∫⁻ z in Set.Ioc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R, ‖H z.1 z.2‖ₑ < ⊤ := by
  have hc : Continuous (fun M : Space →L[ℝ] Space →L[ℝ] Space =>
      ∑ i : Fin 3, ∑ j : Fin 3, ‖M (unitVector i) (unitVector j)‖ ^ 2) := by
    fun_prop
  exact lintegral_box_lt_top (fun z => H z.1 z.2)
    (fun z => ∑ i : Fin 3, ∑ j : Fin 3, ‖H z.1 z.2 (unitVector i) (unitVector j)‖ ^ 2) 9 (by norm_num)
    (fun z => by positivity) (fun z => norm_le_second _)
    (hc.comp_aestronglyMeasurable hv.measurable_secondDeriv).aemeasurable hv.hessian_finite R

def velFun (a : Fin 3) (φ : ℝ) : Space →L[ℝ] ℝ := innerSL ℝ (frameUnit φ a)

def gradFun (a b : Fin 3) (φ : ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (velFun a φ).comp (ContinuousLinearMap.apply ℝ Space (frameUnit φ b))

def slopeFun (a b c : Fin 3) (φ : ℝ) : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (gradFun a b φ).comp (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (frameUnit φ c))

theorem continuous_velFun (a : Fin 3) : Continuous (velFun a) :=
  (innerSL ℝ).continuous.comp (continuous_frameUnit a)

theorem continuous_gradFun (a b : Fin 3) : Continuous (gradFun a b) :=
  (continuous_velFun a).clm_comp ((ContinuousLinearMap.apply ℝ Space).continuous.comp (continuous_frameUnit b))

theorem continuous_slopeFun (a b c : Fin 3) : Continuous (slopeFun a b c) :=
  (continuous_gradFun a b).clm_comp
    ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space)).continuous.comp (continuous_frameUnit c))

theorem velFun_bound (a : Fin 3) (φ : ℝ) (x : Space) : ‖velFun a φ x‖ ≤ ‖x‖ := by
  rw [velFun, innerSL_apply_apply]
  exact (norm_inner_le_norm _ _).trans (by rw [norm_frameUnit, one_mul])

theorem gradFun_bound (a b : Fin 3) (φ : ℝ) (M : Space →L[ℝ] Space) : ‖gradFun a b φ M‖ ≤ ‖M‖ := by
  rw [gradFun, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  refine (velFun_bound a φ _).trans ?_
  exact (M.le_opNorm _).trans (by rw [norm_frameUnit, mul_one])

theorem slopeFun_bound (a b c : Fin 3) (φ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖slopeFun a b c φ M‖ ≤ ‖M‖ := by
  rw [slopeFun, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  refine (gradFun_bound a b φ _).trans ?_
  exact (M.le_opNorm _).trans (by rw [norm_frameUnit, mul_one])

theorem velFun_periodic (a : Fin 3) (φ : ℝ) : velFun a (φ + 2 * Real.pi) = velFun a φ := by
  simp only [velFun, frameUnit_add_two_pi]

theorem gradFun_periodic (a b : Fin 3) (φ : ℝ) : gradFun a b (φ + 2 * Real.pi) = gradFun a b φ := by
  simp only [gradFun, velFun_periodic, frameUnit_add_two_pi]

theorem slopeFun_periodic (a b c : Fin 3) (φ : ℝ) : slopeFun a b c (φ + 2 * Real.pi) = slopeFun a b c φ := by
  simp only [slopeFun, gradFun_periodic, frameUnit_add_two_pi]

theorem labelHarmonic_harmonicMode (m : ℕ) (ν n : ℤ) (hn : Even (n + ν)) :
    labelHarmonic m (harmonicMode ν n) = (ν, n * m) := by
  obtain ⟨t, ht⟩ := hn
  have e : (n + ν) / 2 = t := by omega
  simp only [labelHarmonic, labelTime, labelAzimuth, harmonicMode, e]
  ext
  · simp only
    omega
  · rfl

end Internal.HarmonicProfiles

open Internal.HarmonicProfiles in
theorem harmonic_profiles (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H) (ν n : ℤ)
    (hn : Even (n + ν)) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
      (∀ a, velAt m (harmonicMode ν n) v a p
          = modeVec m n (harmonicCos ν v) p.1 p.2 a + Complex.I * modeVec m n (harmonicSin ν v) p.1 p.2 a) ∧
      (∀ a b, gradAt m (harmonicMode ν n) G a b p
          = gradMode m n (harmonicCos ν G) a b p + Complex.I * gradMode m n (harmonicSin ν G) a b p) ∧
      (∀ a b c, slopeAt m (harmonicMode ν n) H a b c p
          = modeThird m n (harmonicCos ν H) a b c p + Complex.I * modeThird m n (harmonicSin ν H) a b c p) := by
  have hlab := labelHarmonic_harmonicMode m ν n hn
  filter_upwards [ae_integrable_orbit (fun z : ℝ × Space => v z.1 z.2) hv.measurable_velocity
      (box_velocity v G H hv),
    ae_integrable_orbit (fun z : ℝ × Space => G z.1 z.2) hv.measurable_gradient (box_gradient v G H hv),
    ae_integrable_orbit (fun z : ℝ × Space => H z.1 z.2) hv.measurable_secondDeriv (box_secondDeriv v G H hv)]
    with p hpv hpG hpH hp0
  refine ⟨fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · have h := mode_split _ (hpv hp0) (fun τ θ => by simp only [rot_add_two_pi]) (velFun a)
      (continuous_velFun a) (velFun_bound a) (velFun_periodic a) ν (n * m)
    rw [velAt, labelVel, hlab]
    simp only [modeVel, modeAverage, modeVec, zero_add, rot_neg_apply, frameVec_eq, cylPoint_eq_rot,
      harmonicCos, harmonicSin, azimuth]
    simp only [velFun, innerSL_apply_apply, Coercive.Internal.ModeRotation.expFactor] at h
    push_cast at h ⊢
    exact h
  · have h := mode_split _ (hpG hp0) (fun τ θ => by simp only [rot_add_two_pi]) (gradFun a b)
      (continuous_gradFun a b) (gradFun_bound a b) (gradFun_periodic a b) ν (n * m)
    rw [gradAt, labelGrad, hlab]
    simp only [modeGrad, modeAverage, zero_add, rot_unitVector, rot_neg_apply, gradMode, modeMat, frameMat_eq,
      cylPoint_eq_rot, harmonicCos, harmonicSin, azimuth]
    simp only [gradFun, velFun, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, Coercive.Internal.ModeRotation.expFactor] at h
    push_cast at h ⊢
    exact h
  · have h := mode_split _ (hpH hp0) (fun τ θ => by simp only [rot_add_two_pi]) (slopeFun a b c)
      (continuous_slopeFun a b c) (slopeFun_bound a b c) (slopeFun_periodic a b c) ν (n * m)
    rw [slopeAt, labelHess, hlab]
    simp only [modeSecondDeriv, modeAverage, zero_add, rot_unitVector, rot_neg_apply, modeThird, frameThird_eq,
      cylPoint_eq_rot, harmonicCos, harmonicSin, azimuth]
    simp only [slopeFun, gradFun, velFun, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, Coercive.Internal.ModeRotation.expFactor] at h
    push_cast at h ⊢
    exact h

theorem harmonicLift_holds : HarmonicLiftStatement := by
  intro m v G H hv ν
  exact ⟨(harmonic_local v G H hv ν).1, (harmonic_local v G H hv ν).2,
    fun n hn => harmonic_profiles m v G H hv ν n hn⟩

end CellCalculus

end CertCell

end Breakdown
