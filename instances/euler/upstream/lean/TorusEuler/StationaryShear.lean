import TorusEuler.AffineWave
import TorusEuler.Statement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

private def seedDirection (s : ℝ) : Vec3 :=
  EuclideanSpace.single 0 1 + s • EuclideanSpace.single 2 1

private def seedCovector : Vec3 →L[ℝ] ℝ := innerSL ℝ (EuclideanSpace.single 1 1 : Vec3)

@[simp] private theorem seedCovector_apply (x : Vec3) : seedCovector x = x 1 := by
  simp [seedCovector, EuclideanSpace.inner_single_left]

@[simp] private theorem seedDirection_second (s : ℝ) : seedDirection s 1 = 0 := by
  simp [seedDirection]

/-- The stationary shear in (6.1). -/
def stationaryShear (s : ℝ) (x : Vec3) : Vec3 :=
  Real.sin (2 * Real.pi * x 1) • seedDirection s

/-- The gradient of the initial shear at the origin, (6.1). -/
def stationaryShearGradient (s : ℝ) : Vec3 →L[ℝ] Vec3 :=
  (2 * Real.pi : ℝ) • seedCovector.smulRight (seedDirection s)

theorem hasFDerivAt_stationaryShear (s : ℝ) (x : Vec3) :
    HasFDerivAt (stationaryShear s)
      (Real.cos (2 * Real.pi * x 1) • stationaryShearGradient s) x := by
  let k : Vec3 := EuclideanSpace.single 1 1
  let g : ℝ → ℝ := fun z => Real.sin (2 * Real.pi * z)
  have hx : ⟪k, x⟫_ℝ = x 1 := seedCovector_apply x
  have hg : HasDerivAt g (2 * Real.pi * Real.cos (2 * Real.pi * x 1)) ⟪k, x⟫_ℝ := by
    rw [hx]
    simpa only [g, id_eq, mul_one, mul_comm (Real.cos _)] using
      (((hasDerivAt_id (x 1)).const_mul (2 * Real.pi)).sin)
  have h := hasFDerivAt_planeWave g (seedDirection s) k x _ hg
  have hf : (fun y => g ⟪k, y⟫_ℝ • seedDirection s) = stationaryShear s := by
    funext y
    rw [show ⟪k, y⟫_ℝ = y 1 from seedCovector_apply y]
    rfl
  rw [hf] at h
  have hmap : ((2 * Real.pi * Real.cos (2 * Real.pi * x 1)) • innerSL ℝ k).smulRight
      (seedDirection s) = Real.cos (2 * Real.pi * x 1) • stationaryShearGradient s := by
    apply ContinuousLinearMap.ext
    intro y
    change ((2 * Real.pi * Real.cos (2 * Real.pi * x 1)) * seedCovector y) • seedDirection s = _
    simp only [stationaryShearGradient, smul_apply, smulRight_apply, smul_smul]
    congr 1
    ring
  exact hmap ▸ h

theorem spatiallyPeriodic_stationaryShear (s : ℝ) : SpatiallyPeriodic (stationaryShear s) := by
  intro n x
  have hs : 2 * Real.pi * (x + latticeVector n) 1 =
      2 * Real.pi * x 1 + (n 1 : ℝ) * (2 * Real.pi) := by
    simp only [PiLp.add_apply, latticeVector]
    ring
  unfold stationaryShear
  rw [hs, Real.sin_add_int_mul_two_pi]

theorem odd_stationaryShear (s : ℝ) : Function.Odd (stationaryShear s) := by
  intro x
  simp [stationaryShear, mul_neg, Real.sin_neg, neg_smul]

theorem stationaryShear_second (s : ℝ) (x : Vec3) : stationaryShear s x 1 = 0 := by
  simp [stationaryShear]

theorem stationaryShearGradient_sq (s : ℝ) :
    (stationaryShearGradient s).comp (stationaryShearGradient s) = 0 := by
  ext x
  simp [stationaryShearGradient, ← smul_assoc]

theorem divergence_stationaryShear (s : ℝ) (x : Vec3) : divergence (stationaryShear s) x = 0 := by
  rw [divergence, (hasFDerivAt_stationaryShear s x).fderiv]
  simp [Fin.sum_univ_three, stationaryShearGradient]

theorem stationaryShear_advection (s : ℝ) (x : Vec3) :
    fderiv ℝ (stationaryShear s) x (stationaryShear s x) = 0 := by
  rw [(hasFDerivAt_stationaryShear s x).fderiv]
  simp [stationaryShearGradient, stationaryShear_second]

/-- The base shear solves unforced Euler with zero pressure and residual. -/
theorem isEulerSolution_stationaryShear (s : ℝ) {T : ℝ} (hT : 0 < T) :
    IsEulerSolution T (fun _ => stationaryShear s) (fun _ _ => 0) where
  time_pos := hT
  smooth_velocity := by
    have h : ContDiff ℝ ∞ (fun x : Vec3 =>
        Real.sin (2 * Real.pi * seedCovector x) • seedDirection s) := by fun_prop
    change ContDiffOn ℝ ∞ ((stationaryShear s) ∘ Prod.snd) _
    have hs : ContDiff ℝ ∞ (stationaryShear s) := by
      change ContDiff ℝ ∞ (fun x : Vec3 => Real.sin (2 * Real.pi * x 1) • seedDirection s)
      simpa only [seedCovector_apply] using h
    exact (hs.comp contDiff_snd).contDiffOn
  smooth_pressure := contDiffOn_const
  periodic_velocity := fun _ _ => spatiallyPeriodic_stationaryShear s
  periodic_pressure := fun _ _ _ _ => rfl
  mean_zero_pressure := by simp
  momentum := by simp [timeDerivative, stationaryShear_advection]
  incompressible := fun _ _ => divergence_stationaryShear s

/-- Explicit trajectory in (6.2), extended to all real times. -/
def stationaryShearFlow (s t : ℝ) (a : Vec3) : Vec3 := a + t • stationaryShear s a

theorem stationaryShearFlow_second (s t : ℝ) (a : Vec3) : stationaryShearFlow s t a 1 = a 1 := by
  simp [stationaryShearFlow, stationaryShear_second]

theorem stationaryShear_on_flow (s t : ℝ) (a : Vec3) :
    stationaryShear s (stationaryShearFlow s t a) = stationaryShear s a := by
  simp [stationaryShear, stationaryShearFlow_second]

theorem hasDerivAt_stationaryShearFlow (s t : ℝ) (a : Vec3) :
    HasDerivAt (fun r => stationaryShearFlow s r a) (stationaryShear s (stationaryShearFlow s t a)) t := by
  rw [stationaryShear_on_flow]
  simpa only [id_eq, one_smul, stationaryShearFlow] using
    (((hasDerivAt_id t).smul_const (stationaryShear s a)).const_add a)

theorem stationaryShearFlow_inverse (s t : ℝ) (a : Vec3) :
    stationaryShearFlow s (-t) (stationaryShearFlow s t a) = a := by
  unfold stationaryShearFlow at ⊢
  rw [show stationaryShear s (a + t • stationaryShear s a) = stationaryShear s a from
    stationaryShear_on_flow s t a, neg_smul]
  abel

theorem hasFDerivAt_stationaryShearFlow (s t : ℝ) (a : Vec3) :
    HasFDerivAt (stationaryShearFlow s t)
      (ContinuousLinearMap.id ℝ Vec3 +
        (t * Real.cos (2 * Real.pi * a 1)) • stationaryShearGradient s) a := by
  change HasFDerivAt (fun x => x + t • stationaryShear s x) _ a
  simpa only [Pi.add_def, Pi.smul_def, id_eq, smul_smul] using
    (hasFDerivAt_id a).add ((hasFDerivAt_stationaryShear s a).const_smul t)

theorem stationaryShearGradient_origin (s : ℝ) :
    fderiv ℝ (stationaryShear s) 0 = stationaryShearGradient s := by
  rw [(hasFDerivAt_stationaryShear s 0).fderiv]
  simp

theorem stationaryShearFlow_origin (s t : ℝ) : stationaryShearFlow s t 0 = 0 := by
  simp [stationaryShearFlow, stationaryShear]

theorem stationaryShearGradient_couplings (s : ℝ) :
    (stationaryShearGradient s (EuclideanSpace.single 1 1)) 0 = 2 * Real.pi ∧
    (stationaryShearGradient s (EuclideanSpace.single 1 1)) 2 = 2 * Real.pi * s := by
  simp [stationaryShearGradient, seedDirection]

private theorem norm_seedDirection_le {s : ℝ} (hs : |s| ≤ 1) : ‖seedDirection s‖ ≤ 2 := by
  unfold seedDirection
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs, EuclideanSpace.single, PiLp.norm_single, abs_one,
    mul_one]
  linarith

theorem norm_stationaryShear_le {s : ℝ} (hs : |s| ≤ 1) (x : Vec3) : ‖stationaryShear s x‖ ≤ 2 := by
  rw [stationaryShear, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 1 * ‖seedDirection s‖ :=
      mul_le_mul_of_nonneg_right (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
        (norm_nonneg _)
    _ ≤ 2 := by simpa only [one_mul] using norm_seedDirection_le hs

theorem norm_stationaryShearGradient_le {s : ℝ} (hs : |s| ≤ 1) :
    ‖stationaryShearGradient s‖ ≤ 4 * Real.pi := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hcov : ‖seedCovector‖ = 1 := by
    rw [seedCovector, innerSL_apply_norm]
    simp only [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs, abs_one]
  rw [stationaryShearGradient, norm_smul, Real.norm_eq_abs, abs_of_pos hπ, norm_smulRight_apply,
    hcov, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left (norm_seedDirection_le hs) hπ.le]

theorem stationaryShearDeformation_inverse (s c : ℝ) :
    ((ContinuousLinearMap.id ℝ Vec3 + c • stationaryShearGradient s).comp
      (ContinuousLinearMap.id ℝ Vec3 - c • stationaryShearGradient s)) =
      ContinuousLinearMap.id ℝ Vec3 ∧
    ((ContinuousLinearMap.id ℝ Vec3 - c • stationaryShearGradient s).comp
      (ContinuousLinearMap.id ℝ Vec3 + c • stationaryShearGradient s)) =
      ContinuousLinearMap.id ℝ Vec3 := by
  have hs (x : Vec3) : stationaryShearGradient s (stationaryShearGradient s x) = 0 :=
    DFunLike.congr_fun (stationaryShearGradient_sq s) x
  constructor <;> apply ContinuousLinearMap.ext <;> intro x <;> simp [hs]

end
end TorusEuler
