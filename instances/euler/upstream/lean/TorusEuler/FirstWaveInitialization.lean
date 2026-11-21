import TorusEuler.AffineExistence
import TorusEuler.MovingCoordinateWaveVector
import TorusEuler.StationaryShear
import TorusEuler.TransportedPhase
import TorusEuler.WaveProfile
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! The first wave at the origin of the stationary shear in §6.1. -/

open Set ContinuousLinearMap
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

private abbrev axis (i : Fin 3) : Vec3 := EuclideanSpace.single i 1

private theorem norm_axis (i : Fin 3) : ‖axis i‖ = 1 := by
  simp [axis, EuclideanSpace.single, PiLp.norm_single]

private theorem axis_ne_zero (i : Fin 3) : axis i ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_axis]; exact one_ne_zero)

/-- The first-wave covector at a material label is the transpose of the
inverse stationary-shear deformation applied to the prescribed covector. -/
def firstWaveTransportedCovector (s freq t : ℝ) (a : Vec3) : Vec3 :=
  (ContinuousLinearMap.id ℝ Vec3 -
    (t * Real.cos (2 * Real.pi * a 1)) • stationaryShearGradient s).adjoint (freq • axis 0)

theorem firstWaveTransportedCovector_zero (s freq : ℝ) (a : Vec3) :
    firstWaveTransportedCovector s freq 0 a = freq • EuclideanSpace.single 0 1 := by
  simp [firstWaveTransportedCovector]

/-- The explicit inverse shear flow produces this covector as the gradient
of the Eulerian phase, including at labels away from the origin. -/
theorem hasGradientAt_firstWaveTransportedPhase (s freq t : ℝ) (a : Vec3) :
    HasGradientAt (fun x => ⟪freq • EuclideanSpace.single 0 1, stationaryShearFlow s (-t) x⟫_ℝ)
      (firstWaveTransportedCovector s freq t a) (stationaryShearFlow s t a) := by
  have h := hasFDerivAt_stationaryShearFlow s (-t) (stationaryShearFlow s t a)
  rw [stationaryShearFlow_second] at h
  let c := Real.cos (2 * Real.pi * a 1)
  let B := stationaryShearGradient s
  have hmap : ContinuousLinearMap.id ℝ Vec3 + ((-t) * c) • B =
      ContinuousLinearMap.id ℝ Vec3 - (t * c) • B := by
    apply ContinuousLinearMap.ext
    intro y
    change y + ((-t) * c) • B y = y - (t * c) • B y
    rw [sub_eq_add_neg, neg_mul, _root_.neg_smul]
  rw [hmap] at h
  simpa only [firstWaveTransportedCovector] using
    hasGradientAt_transportedPhase (A := fun u => stationaryShearFlow s (-u)) (t := t)
      (k := freq • axis 0) h

/-- The shear gradient seen by each moving label is independent of time. -/
theorem firstWave_shearGradient_onTrajectory (s t : ℝ) (a : Vec3) :
    fderiv ℝ (stationaryShear s) (stationaryShearFlow s t a) =
      Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s := by
  rw [(hasFDerivAt_stationaryShear s (stationaryShearFlow s t a)).fderiv,
    stationaryShearFlow_second]

/-- In each material label the covector solves the affine wave equation
with the stationary, label-dependent shear gradient. -/
theorem hasDerivAt_firstWaveTransportedCovector (s freq t : ℝ) (a : Vec3) :
    HasDerivAt (fun u => firstWaveTransportedCovector s freq u a)
      (-((Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s).adjoint
        (firstWaveTransportedCovector s freq t a))) t := by
  let B := stationaryShearGradient s
  let c := Real.cos (2 * Real.pi * a 1)
  let k₀ : Vec3 := freq • axis 0
  let k₁ := B.adjoint k₀
  have hB : B.adjoint.comp B.adjoint = 0 := by
    rw [← adjoint_comp, stationaryShearGradient_sq s, map_zero]
  have hk : B.adjoint k₁ = 0 := by
    simpa only [comp_apply, zero_apply] using DFunLike.congr_fun hB k₀
  have hEq (u : ℝ) : firstWaveTransportedCovector s freq u a = k₀ - (u * c) • k₁ := by
    change (ContinuousLinearMap.id ℝ Vec3 - (u * c) • B).adjoint k₀ = _
    simp only [map_sub, map_smul, sub_apply, smul_apply, adjoint_id, id_apply, k₁]
  have hfun : (fun u => firstWaveTransportedCovector s freq u a) = fun u => k₀ - (u * c) • k₁ :=
    funext hEq
  rw [hfun, hEq t]
  have hd : HasDerivAt (fun u : ℝ => k₀ - (u * c) • k₁) (-(c • k₁)) t := by
    simpa only [id_eq, one_mul] using
      ((((hasDerivAt_id t).mul_const c).smul_const k₁).const_sub k₀)
  exact hd.congr_deriv (by
    change -(c • k₁) = -((c • B).adjoint (k₀ - (t * c) • k₁))
    rw [map_smul, smul_apply, map_sub, B.adjoint.map_smul (t * c) k₁, hk, smul_zero, sub_zero])

/-- The seed of (6.3) at the origin. Its initial direction is unchanged
by the transverse projection, and it is normalized by the attained
maximum of its length over the closed slab. -/
structure FirstWaveOrigin (s T freq : ℝ) where
  covector : ℝ → Vec3
  amplitude : ℝ → Vec3
  scale : ℝ
  scale_pos : 0 < scale
  covector_initial : covector 0 = freq • EuclideanSpace.single 0 1
  amplitude_initial : amplitude 0 = scale • EuclideanSpace.single 1 1
  covector_equation : ∀ t ∈ Icc 0 T,
    HasDerivWithinAt covector (-((stationaryShearGradient s).adjoint (covector t))) (Icc 0 T) t
  amplitude_equation : ∀ t ∈ Icc 0 T,
    HasDerivWithinAt amplitude
      (affineWaveAmplitudeOperator (stationaryShearGradient s) (covector t) (amplitude t))
      (Icc 0 T) t
  transverse : ∀ t ∈ Icc 0 T, covector t ≠ 0 ∧ amplitude t ≠ 0 ∧ ⟪covector t, amplitude t⟫_ℝ = 0
  norm_le_peak : ∀ t ∈ Icc 0 T, ‖amplitude t‖ ≤ freq ^ (-(3 / 4) : ℝ)
  attains_peak : ∃ t ∈ Icc 0 T, ‖amplitude t‖ = freq ^ (-(3 / 4) : ℝ)

/-- The first-wave seed exists on the whole prescribed interval, with
the exact maximum `λ^(-3/4)` from (6.3). -/
theorem firstWaveOrigin_exists {s T freq : ℝ} (hT : 0 ≤ T) (hf : 0 < freq) :
    Nonempty (FirstWaveOrigin s T freq) := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  have hk₀ : freq • axis 0 ≠ 0 := smul_ne_zero hf.ne' (axis_ne_zero 0)
  have ha₀ : axis 1 ≠ 0 := axis_ne_zero 1
  have hperp₀ : ⟪freq • axis 0, axis 1⟫_ℝ = 0 := by
    simp [axis, real_inner_smul_left, EuclideanSpace.inner_single_left]
  obtain ⟨k, a, hk₀', ha₀', hk, ha, htrans⟩ :=
    affineWave_exists_Icc (D := fun _ => stationaryShearGradient s)
      h0T continuousOn_const hk₀ ha₀ hperp₀
  have hnormc : ContinuousOn (fun t => ‖a t‖) (Icc 0 T) :=
    (HasDerivWithinAt.continuousOn ha).norm
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, h0T⟩ hnormc
  have hM : 0 < ‖a tmax‖ := norm_pos_iff.mpr (htrans tmax htmax).2.1
  let c : ℝ := freq ^ (-(3 / 4) : ℝ) / ‖a tmax‖
  have hc : 0 < c := div_pos (Real.rpow_pos_of_pos hf _) hM
  have hpeak (t : ℝ) : ‖c • a t‖ = c * ‖a t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hcm : c * ‖a tmax‖ = freq ^ (-(3 / 4) : ℝ) := div_mul_cancel₀ _ hM.ne'
  refine ⟨⟨k, fun t => c • a t, c, hc, hk₀', by rw [ha₀'], hk, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht
    have h := (ha t ht).const_smul c
    rw [← affineWaveAmplitudeOperator_apply, ← map_smul] at h
    exact h
  · intro t ht
    obtain ⟨hkt, hat, hka⟩ := htrans t ht
    exact ⟨hkt, smul_ne_zero hc.ne' hat, by rw [real_inner_smul_right, hka, mul_zero]⟩
  · intro t ht
    rw [hpeak, ← hcm]
    exact mul_le_mul_of_nonneg_left (hmax ht) hc.le
  · exact ⟨tmax, htmax, (hpeak tmax).trans hcm⟩

/-- The projection used to initialize the label-dependent seed leaves the
first-wave amplitude unchanged at every label at time zero. -/
theorem FirstWaveOrigin.initial_projection {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hT : 0 ≤ T) (a : Vec3) :
    let k := firstWaveTransportedCovector s freq 0 a
    w.amplitude 0 - (⟪k, w.amplitude 0⟫_ℝ / ‖k‖ ^ 2) • k = w.amplitude 0 := by
  dsimp only
  rw [firstWaveTransportedCovector_zero, ← w.covector_initial,
    (w.transverse 0 (left_mem_Icc.mpr hT)).2.2, zero_div, zero_smul, sub_zero]

/-- The ODE covector used in the central seed is the actual transported
covector of the initial phase on the whole window. -/
theorem FirstWaveOrigin.covector_eq_transported {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hT : 0 ≤ T) :
    EqOn w.covector (fun t => firstWaveTransportedCovector s freq t 0) (Icc 0 T) := by
  apply linearODE_unique_of_mem (A := fun _ => -((stationaryShearGradient s).adjoint))
    ordConnected_Icc (left_mem_Icc.mpr hT) continuousOn_const
  · intro t ht
    simpa only [neg_apply] using w.covector_equation t ht
  · intro t _
    simpa only [PiLp.zero_apply, mul_zero, Real.cos_zero, one_smul, neg_apply] using
      (hasDerivAt_firstWaveTransportedCovector s freq t 0).hasDerivWithinAt (s := Icc 0 T)
  · rw [w.covector_initial, firstWaveTransportedCovector_zero]

/-- For every label the affine amplitude ODE has a transverse solution
with the same initial amplitude and the actual transported covector. -/
theorem FirstWaveOrigin.exists_seed_at_label {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hT : 0 ≤ T) (a : Vec3) :
    let k (t : ℝ) := firstWaveTransportedCovector s freq t a
    let B := Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s
    ∃ b : ℝ → Vec3, b 0 = w.amplitude 0 ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt b (affineWaveAmplitudeOperator B (k t) (b t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, k t ≠ 0 ∧ b t ≠ 0 ∧ ⟪k t, b t⟫_ℝ = 0 := by
  let k (t : ℝ) := firstWaveTransportedCovector s freq t a
  let B := Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  obtain ⟨hk₀, hb₀, hperp₀⟩ := w.transverse 0 h0
  obtain ⟨ka, b, hka₀, hb, hka, hda, hchecks⟩ :=
    affineWave_exists_Icc (D := fun _ => B) h0 continuousOn_const hk₀ hb₀ hperp₀
  have hsame : EqOn ka k (Icc 0 T) := by
    apply linearODE_unique_of_mem (A := fun _ => -(B.adjoint)) ordConnected_Icc h0 continuousOn_const
    · intro t ht
      simpa only [neg_apply] using hka t ht
    · intro t _
      simpa only [neg_apply] using
        (hasDerivAt_firstWaveTransportedCovector s freq t a).hasDerivWithinAt (s := Icc 0 T)
    · rw [hka₀, w.covector_initial]
      exact (firstWaveTransportedCovector_zero s freq a).symm
  refine ⟨b, hb, fun t ht => ?_, fun t ht => ?_⟩
  · change HasDerivWithinAt b (affineWaveAmplitudeOperator B (k t) (b t)) (Icc 0 T) t
    rw [← hsame ht, affineWaveAmplitudeOperator_apply]
    exact hda t ht
  · change k t ≠ 0 ∧ b t ≠ 0 ∧ ⟪k t, b t⟫_ℝ = 0
    rw [← hsame ht]
    exact hchecks t ht

private theorem norm_reflected_amplitude (k w : Vec3) :
    ‖-w + (2 * ⟪k, w⟫_ℝ / ‖k‖ ^ 2) • k‖ = ‖w‖ := by
  convert (Submodule.reflection (ℝ ∙ k)).norm_map w using 1
  congr 1
  rw [Submodule.reflection_singleton_apply, two_smul ℕ, ← two_smul ℝ, smul_smul,
    mul_div_assoc, sub_eq_neg_add]
  rfl

private theorem affineAmplitude_norm_upper {B : Vec3 →L[ℝ] Vec3} {k b : ℝ → Vec3}
    {T u v : ℝ} (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T) (huv : u ≤ v)
    (hb : ∀ t ∈ Icc 0 T, HasDerivWithinAt b (affineWaveAmplitudeOperator B (k t) (b t))
      (Icc 0 T) t) :
    ‖b v‖ ≤ ‖b u‖ * Real.exp (‖B‖ * (v - u)) := by
  have hsub : Icc u v ⊆ Icc 0 T := Icc_subset_Icc hu.1 hv.2
  have hd (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivWithinAt b (affineWaveAmplitudeOperator B (k t) (b t)) (Icc u v) t :=
    (hb t (hsub ht)).mono hsub
  rw [← gronwallBound_ε0]
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivWithinAt.continuousOn hd)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    le_rfl _ v (right_mem_Icc.mpr huv)
  intro t _
  rw [add_zero, affineWaveAmplitudeOperator_apply, norm_reflected_amplitude]
  exact B.le_opNorm (b t)

private theorem hasDerivWithinAt_log_amplitude_norm {B : Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    {J : Set ℝ} {t : ℝ} (ha₀ : a t ≠ 0) (hka : ⟪k t, a t⟫_ℝ = 0)
    (ha : HasDerivWithinAt a (affineWaveAmplitudeOperator B (k t) (a t)) J t) :
    HasDerivWithinAt (fun u => Real.log ‖a u‖) (-⟪a t, B (a t)⟫_ℝ / ‖a t‖ ^ 2) J t := by
  rw [affineWaveAmplitudeOperator_apply] at ha
  have hsq : HasDerivWithinAt (fun u => ‖a u‖ ^ 2) (-2 * ⟪a t, B (a t)⟫_ℝ) J t := by
    refine ha.norm_sq.congr_deriv ?_
    rw [inner_add_right, inner_neg_right, real_inner_smul_right,
      show ⟪a t, k t⟫_ℝ = 0 from (real_inner_comm (k t) (a t)).trans hka, mul_zero, add_zero]
    ring
  have hform : (fun u => (1 / 2 : ℝ) * Real.log (‖a u‖ ^ 2)) = (fun u => Real.log ‖a u‖) := by
    funext u
    rw [Real.log_pow]
    ring
  rw [← hform]
  exact ((hsq.log (pow_ne_zero _ (norm_ne_zero_iff.mpr ha₀))).const_mul _).congr_deriv (by ring)

private theorem abs_amplitude_log_rate_le (B : Vec3 →L[ℝ] Vec3) {a : Vec3} (ha : a ≠ 0) :
    |-⟪a, B a⟫_ℝ / ‖a‖ ^ 2| ≤ ‖B‖ := by
  have hA : 0 < ‖a‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr ha) _
  rw [abs_div, abs_neg, abs_of_pos hA]
  apply (div_le_iff₀ hA).mpr
  calc
    |⟪a, B a⟫_ℝ| ≤ ‖a‖ * ‖B a‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖a‖ * (‖B‖ * ‖a‖) := mul_le_mul_of_nonneg_left (B.le_opNorm a) (norm_nonneg _)
    _ = ‖B‖ * ‖a‖ ^ 2 := by ring

private theorem affineAmplitude_norm_lower {B : Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    {T u v : ℝ} (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T) (huv : u ≤ v)
    (ha : ∀ t ∈ Icc 0 T, HasDerivWithinAt a (affineWaveAmplitudeOperator B (k t) (a t))
      (Icc 0 T) t) (htrans : ∀ t ∈ Icc 0 T, a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) :
    ‖a u‖ * Real.exp (-‖B‖ * (v - u)) ≤ ‖a v‖ := by
  have hsub : Icc u v ⊆ Icc 0 T := Icc_subset_Icc hu.1 hv.2
  have hd (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivWithinAt (fun x => Real.log ‖a x‖) (-⟪a t, B (a t)⟫_ℝ / ‖a t‖ ^ 2)
        (Icc u v) t :=
    (hasDerivWithinAt_log_amplitude_norm (htrans t (hsub ht)).1 (htrans t (hsub ht)).2
      (ha t (hsub ht))).mono hsub
  have hdle (t : ℝ) (ht : t ∈ Ico u v) :
      ‖-⟪a t, B (a t)⟫_ℝ / ‖a t‖ ^ 2‖ ≤ ‖B‖ :=
    Real.norm_eq_abs _ ▸ abs_amplitude_log_rate_le B (htrans t (hsub (Ico_subset_Icc_self ht))).1
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hdle v (right_mem_Icc.mpr huv)
  rw [Real.norm_eq_abs] at h
  have hlog : Real.log ‖a u‖ + (-‖B‖ * (v - u)) ≤ Real.log ‖a v‖ := by
    linarith only [(abs_le.mp h).1]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr (htrans u hu).1),
    Real.exp_log (norm_pos_iff.mpr (htrans v hv).1)] at hexp
  exact hexp

private theorem exp_le_two_of_small {x : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 4) :
    Real.exp x ≤ 2 := by
  have h := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx₀]; linarith)
  rw [abs_of_nonneg hx₀] at h
  linarith only [(abs_le.mp h).2, hx]

/-- The weighted forward estimate at the origin, for any solution of the
linear amplitude equation and any start time in the closed slab. -/
theorem FirstWaveOrigin.weighted_forward {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8)
    {D u v : ℝ} (hD : 2 ≤ D) (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T) (huv : u ≤ v)
    {b : ℝ → Vec3} (hb : ∀ t ∈ Icc 0 T, HasDerivWithinAt b
      (affineWaveAmplitudeOperator (stationaryShearGradient s) (w.covector t) (b t)) (Icc 0 T) t) :
    let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖w.amplitude t‖
    ‖b v‖ / γ v ≤ D * (‖b u‖ / γ u) := by
  let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖w.amplitude t‖
  let L := ‖stationaryShearGradient s‖ * (v - u)
  have hL₀ : 0 ≤ L := mul_nonneg (norm_nonneg _) (sub_nonneg.mpr huv)
  have hL : L ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left (show v - u ≤ T by linarith [hu.1, hv.2])
      (norm_nonneg (stationaryShearGradient s))
    dsimp only [L]
    linarith only [h, hsmall]
  have hγ t (ht : t ∈ Icc 0 T) : 0 < γ t :=
    mul_pos (Real.rpow_pos_of_pos hf _) (norm_pos_iff.mpr (w.transverse t ht).2.1)
  have hLow := affineAmplitude_norm_lower hu hv huv w.amplitude_equation
    (fun t ht => (w.transverse t ht).2)
  have hγLow : γ u * Real.exp (-L) ≤ γ v := by
    unfold γ L
    rw [mul_assoc, ← neg_mul]
    exact mul_le_mul_of_nonneg_left hLow (Real.rpow_nonneg hf.le _)
  have hγL : γ u * Real.exp L ≤ D * γ v := by
    have hEq : Real.exp L = Real.exp (-L) * Real.exp (2 * L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (γ u * Real.exp (-L)) * Real.exp (2 * L) := by
        simpa only [mul_assoc] using congrArg (fun x : ℝ => γ u * x) hEq
      _ ≤ γ v * Real.exp (2 * L) := mul_le_mul_of_nonneg_right hγLow (Real.exp_pos _).le
      _ ≤ γ v * D := mul_le_mul_of_nonneg_left
        ((exp_le_two_of_small (by linarith) (by linarith)).trans hD) (hγ v hv).le
      _ = _ := mul_comm _ _
  change ‖b v‖ / γ v ≤ D * (‖b u‖ / γ u)
  apply (div_le_iff₀ (hγ v hv)).mpr
  calc
    ‖b v‖ ≤ ‖b u‖ * Real.exp L := affineAmplitude_norm_upper hu hv huv hb
    _ = (‖b u‖ / γ u) * (γ u * Real.exp L) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (hγ u hu).ne']
    _ ≤ (‖b u‖ / γ u) * (D * γ v) :=
      mul_le_mul_of_nonneg_left hγL (div_nonneg (norm_nonneg _) (hγ u hu).le)
    _ = _ := by ring

/-- The strength of the first wave at activation lies between half the
prescribed scale and that scale, as in Lemma 6.1. -/
theorem FirstWaveOrigin.initial_strength {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) :
    freq ^ (1 / 4 : ℝ) / 2 ≤ ‖w.covector 0‖ * ‖w.amplitude 0‖ ∧
      ‖w.covector 0‖ * ‖w.amplitude 0‖ ≤ freq ^ (1 / 4 : ℝ) := by
  obtain ⟨tmax, htmax, hmax⟩ := w.attains_peak
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, htmax.1.trans htmax.2⟩
  let L := ‖stationaryShearGradient s‖ * tmax
  have hL₀ : 0 ≤ L := mul_nonneg (norm_nonneg _) htmax.1
  have hL : L ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left htmax.2 (norm_nonneg (stationaryShearGradient s))
    dsimp only [L]
    linarith only [h, hsmall]
  have hx := affineAmplitude_norm_upper h0T htmax htmax.1 w.amplitude_equation
  rw [sub_zero, hmax] at hx
  have hLower : freq ^ (-(3 / 4) : ℝ) / 2 ≤ ‖w.amplitude 0‖ := by
    linarith only [hx, mul_le_mul_of_nonneg_left (exp_le_two_of_small hL₀ hL)
      (norm_nonneg (w.amplitude 0))]
  have hcov : ‖w.covector 0‖ = freq := by
    rw [w.covector_initial, norm_smul, Real.norm_eq_abs, abs_of_pos hf, norm_axis, mul_one]
  have hfPow : freq * freq ^ (-(3 / 4) : ℝ) = freq ^ (1 / 4 : ℝ) := by
    nth_rw 1 [← Real.rpow_one freq]
    rw [← Real.rpow_add hf]
    norm_num
  rw [hcov, ← hfPow]
  exact ⟨by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hLower hf.le,
    mul_le_mul_of_nonneg_left (w.norm_le_peak 0 h0T) hf.le⟩

open MovingWaveVector in
/-- At activation the preceding frame is the coordinate frame, and its
two shear couplings are exactly (6.4). -/
theorem FirstWaveOrigin.initial_couplings {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) :
    entry (frame w.covector w.amplitude 0) (stationaryShearGradient s) 0 1 = 2 * Real.pi ∧
      entry (frame w.covector w.amplitude 0) (stationaryShearGradient s) 2 1 = 2 * Real.pi * s := by
  have hcross : cross3 (axis 0) (axis 1) = axis 2 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [cross3, cross_apply, axis, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hframe : frame w.covector w.amplitude 0 = ![axis 0, axis 1, axis 2] := by
    simp only [frame, w.covector_initial, w.amplitude_initial, NormedSpace.normalize_smul_of_pos hf,
      NormedSpace.normalize_smul_of_pos w.scale_pos,
      NormedSpace.normalize_eq_self_of_norm_eq_one (norm_axis 0),
      NormedSpace.normalize_eq_self_of_norm_eq_one (norm_axis 1), hcross]
  rw [hframe]
  simpa only [entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, EuclideanSpace.inner_single_left, map_one, one_mul] using
    stationaryShearGradient_couplings s

/-- The actual periodic phase profile contributes the prescribed rank-one
gradient at activation whenever the spatial envelope equals one near the origin. -/
theorem FirstWaveOrigin.initial_profile_gradient {s T freq h : ℝ} (w : FirstWaveOrigin s T freq)
    (hh : 0 < h) (hh₁ : h ≤ 1) {g : Vec3 → ℝ} (hg : g =ᶠ[nhds 0] (fun _ => 1)) :
    HasFDerivAt (fun y => g y • (waveProfile h ⟪w.covector 0, y⟫_ℝ • w.amplitude 0))
      ((innerSL ℝ (w.covector 0)).smulRight (w.amplitude 0)) 0 := by
  have hF : HasDerivAt (waveProfile h) 1 ⟪w.covector 0, 0⟫_ℝ := by
    rw [inner_zero_right]
    exact hasDerivAt_waveProfile_zero hh hh₁
  have hd := hasFDerivAt_planeWave (waveProfile h) (w.amplitude 0) (w.covector 0) 0 1 hF
  rw [one_smul] at hd
  exact hd.congr_of_eventuallyEq (hg.mono fun y hy => by simp only [hy, one_smul])

private theorem norm_signed_two_axes_le {x y z : Vec3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℝ = 0) {a b : ℝ}
    (ha : a ^ 2 = ⟪x, z⟫_ℝ ^ 2) (hb : b ^ 2 = ⟪y, z⟫_ℝ ^ 2) :
    ‖a • x + b • y‖ ≤ ‖z‖ := by
  have hyx : ⟪y, x⟫_ℝ = 0 := (real_inner_comm x y).trans hxy
  have hnorm (p q : ℝ) : ‖p • x + q • y‖ ^ 2 = p ^ 2 + q ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hxy, hyx, norm_smul, hx, hy, mul_one, Real.norm_eq_abs, sq_abs]
    ring
  let Z := ⟪x, z⟫_ℝ • x + ⟪y, z⟫_ℝ • y
  have hself : ‖Z‖ ^ 2 = ⟪Z, z⟫_ℝ := by
    unfold Z
    rw [hnorm, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hZ : ‖Z‖ ≤ ‖z‖ := by
    by_cases hh : ‖Z‖ = 0
    · rw [hh]
      exact norm_nonneg _
    have hpos : 0 < ‖Z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hh)
    have hineq := (le_abs_self _).trans (abs_real_inner_le_norm Z z)
    rw [← hself] at hineq
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [pow_two, mul_comm] using hineq)
  have heq : ‖a • x + b • y‖ ^ 2 = ‖Z‖ ^ 2 := by
    unfold Z
    rw [hnorm, hnorm, ha, hb]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq).trans_le hZ

private theorem trace_stationaryShearGradient (s : ℝ) :
    LinearMap.trace ℝ Vec3 (stationaryShearGradient s).toLinearMap = 0 := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, stationaryShearGradient,
    Fin.sum_univ_three]

open MovingWaveVector in
/-- The coupling remains at least `π` throughout the first-wave window.
The frame derivatives each have norm at most the shear norm. -/
theorem FirstWaveOrigin.first_coupling_lower {s T freq : ℝ} (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) (hs : |s| ≤ 1) (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Real.pi ≤ entry (frame w.covector w.amplitude t) (stationaryShearGradient s) 0 1 := by
  let B := stationaryShearGradient s
  let e := frame w.covector w.amplitude
  let ν (u : ℝ) := entry (e u) B 0 1
  let η (u : ℝ) := entry (e u) B 2 1
  let χ (u : ℝ) := entry (e u) B 0 2
  let d₁ (u : ℝ) := (-ν u) • e u 1 - χ u • e u 2
  let d₂ (u : ℝ) := ν u • e u 0 - η u • e u 2
  have hFrame (u : ℝ) (hu : u ∈ Icc 0 T) : Orthonormal ℝ (e u) := by
    obtain ⟨hk, ha, hka⟩ := w.transverse u hu
    exact orthonormal_movingFrame hk ha hka
  have hDeriv (u : ℝ) (hu : u ∈ Icc 0 T) :
      HasDerivWithinAt (fun x => e x 0) (d₁ u) (Icc 0 T) u ∧
      HasDerivWithinAt (fun x => e x 1) (d₂ u) (Icc 0 T) u := by
    obtain ⟨hk, ha, hka⟩ := w.transverse u hu
    have hA := w.amplitude_equation u hu
    rw [affineWaveAmplitudeOperator_apply] at hA
    have h := hasDerivWithinAt_movingFrame hu B (trace_stationaryShearGradient s)
      hk ha hka (w.covector_equation u hu) hA
    exact ⟨h.1, h.2.1⟩
  have hDerivNorm (u : ℝ) (hu : u ∈ Icc 0 T) : ‖d₁ u‖ ≤ ‖B‖ ∧ ‖d₂ u‖ ≤ ‖B‖ := by
    have he := hFrame u hu
    have hν : ⟪e u 1, B.adjoint (e u 0)⟫_ℝ = ν u :=
      (B.adjoint_inner_right _ _).trans (real_inner_comm _ _)
    have hχ : ⟪e u 2, B.adjoint (e u 0)⟫_ℝ = χ u :=
      (B.adjoint_inner_right _ _).trans (real_inner_comm _ _)
    constructor
    · calc
        ‖d₁ u‖ ≤ ‖B.adjoint (e u 0)‖ := by
          unfold d₁
          rw [sub_eq_add_neg, ← neg_smul]
          exact norm_signed_two_axes_le (he.norm_eq_one 1) (he.norm_eq_one 2)
            (he.inner_eq_zero (by decide : (1 : Fin 3) ≠ 2))
            (by rw [hν]; ring) (by rw [hχ]; ring)
        _ ≤ ‖B‖ := by
          simpa only [LinearIsometryEquiv.norm_map, he.norm_eq_one 0, mul_one] using
            B.adjoint.le_opNorm (e u 0)
    · calc
        ‖d₂ u‖ ≤ ‖B (e u 1)‖ := by
          unfold d₂
          rw [sub_eq_add_neg, ← neg_smul]
          exact norm_signed_two_axes_le (he.norm_eq_one 0) (he.norm_eq_one 2)
            (he.inner_eq_zero (by decide : (0 : Fin 3) ≠ 2))
            rfl (by change (-η u) ^ 2 = (η u) ^ 2; ring)
        _ ≤ ‖B‖ := by simpa only [he.norm_eq_one 1, mul_one] using B.le_opNorm (e u 1)
  let dν (u : ℝ) := ⟪e u 0, B (d₂ u)⟫_ℝ + ⟪d₁ u, B (e u 1)⟫_ℝ
  have hDν (u : ℝ) (hu : u ∈ Icc 0 T) : HasDerivWithinAt ν (dν u) (Icc 0 T) u :=
    ((hDeriv u hu).1).inner ℝ (B.hasFDerivAt.comp_hasDerivWithinAt u (hDeriv u hu).2)
  have hDνle (u : ℝ) (hu : u ∈ Icc 0 T) : ‖dν u‖ ≤ 2 * ‖B‖ ^ 2 := by
    have he := hFrame u hu
    have h₁ : |⟪e u 0, B (d₂ u)⟫_ℝ| ≤ ‖B‖ ^ 2 := by
      have h := abs_real_inner_le_norm (e u 0) (B (d₂ u))
      rw [he.norm_eq_one 0, one_mul] at h
      rw [pow_two]
      exact h.trans ((B.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hDerivNorm u hu).2 (norm_nonneg _)))
    have h₂ : |⟪d₁ u, B (e u 1)⟫_ℝ| ≤ ‖B‖ ^ 2 := by
      have h := abs_real_inner_le_norm (d₁ u) (B (e u 1))
      have hB : ‖B (e u 1)‖ ≤ ‖B‖ := by
        simpa only [he.norm_eq_one 1, mul_one] using B.le_opNorm (e u 1)
      rw [pow_two]
      exact h.trans (mul_le_mul (hDerivNorm u hu).1 hB (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (by linarith only [h₁, h₂])
  have hdiff := norm_image_sub_le_of_norm_deriv_le_segment' hDν
    (fun u hu => hDνle u (Ico_subset_Icc_self hu)) t ht
  rw [Real.norm_eq_abs, sub_zero] at hdiff
  have hsmall' : 2 * ‖B‖ ^ 2 * t ≤ ‖B‖ / 4 := by
    have h := mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ 2 * ‖B‖ ^ 2 by positivity)
    have hb := mul_le_mul_of_nonneg_right hsmall (norm_nonneg B)
    change T * ‖B‖ * ‖B‖ ≤ 1 / 8 * ‖B‖ at hb
    nlinarith only [h, hb]
  have hmax : ‖B‖ / 4 ≤ Real.pi := by linarith [norm_stationaryShearGradient_le hs]
  have hinit : ν 0 = 2 * Real.pi := (w.initial_couplings hf).1
  change Real.pi ≤ ν t
  linarith only [(abs_le.mp (hdiff.trans (hsmall'.trans hmax))).1, hinit]

end
end TorusEuler
