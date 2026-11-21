import TorusEuler.ActivationProfiles
import TorusEuler.PeriodicLerayL2
import TorusEuler.StationaryShear
import TorusEuler.TorusLabelFlow
import TorusEuler.WaveCurl
import TorusEuler.WaveDivergence
import TorusEuler.WaveProfile
import Mathlib.Analysis.Real.Pi.Bounds

/-! The stationary parent in (T1)–(T3) of Theorem 7.1. -/

open Filter Set MeasureTheory UnitAddTorus ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

/-- The positive second-coordinate Fourier frequency of the shear. -/
def stationaryShearMode : Fin 3 → ℤ := Pi.single 1 1

private theorem stationaryShearMode_ne_neg : stationaryShearMode ≠ -stationaryShearMode := by
  intro h
  have h₁ := congrFun h 1
  norm_num [stationaryShearMode] at h₁

private def shearFourierDirection (s : ℝ) : ComplexEuclideanVec3 :=
  periodicComplexifyVector
    ((EuclideanSpace.single 0 1 : Vec3) + s • EuclideanSpace.single 2 1)

private theorem shearFourierDirection_ne_zero (s : ℝ) : shearFourierDirection s ≠ 0 := by
  intro h
  have h₀ := congrArg (fun z : ComplexEuclideanVec3 => z 0) h
  norm_num [shearFourierDirection, PiLp.add_apply, PiLp.smul_apply,
    show (0 : Fin 3) ≠ 2 by decide] at h₀

private def shearFourierFactor : ℂ := 1 / (2 * Complex.I)

private theorem shearFourierFactor_ne_zero : shearFourierFactor ≠ 0 :=
  div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)

/-- The two nonzero coefficients of the complexified real shear are the
sine coefficients times the fixed shear direction. -/
def stationaryShearFourierCoeff (s : ℝ) (k : Fin 3 → ℤ) : ComplexEuclideanVec3 := by
  classical
  exact if k = stationaryShearMode then shearFourierFactor • shearFourierDirection s else
    if k = -stationaryShearMode then (-shearFourierFactor) • shearFourierDirection s else 0

/-- The torus field given by the two signed second-coordinate modes. -/
def stationaryShearComplexTorus (s : ℝ) : UnitAddTorus (Fin 3) → ComplexEuclideanVec3 := by
  classical
  exact finiteFourierSum {stationaryShearMode, -stationaryShearMode} (stationaryShearFourierCoeff s)

private theorem fourierMode_shear_signed (x : Vec3) :
    fourierMode stationaryShearMode x =
      Complex.exp (((2 * Real.pi * x 1 : ℝ) : ℂ) * Complex.I) ∧
    fourierMode (-stationaryShearMode) x =
      Complex.exp (-((2 * Real.pi * x 1 : ℝ) : ℂ) * Complex.I) := by
  constructor <;> rw [fourierMode_eq_exp] <;> congr 1 <;>
    simp [stationaryShearMode, Fin.sum_univ_three] <;> ring

private theorem sine_from_signed_modes (z : ℂ) :
    Complex.exp (z * Complex.I) * shearFourierFactor +
      Complex.exp ((-z) * Complex.I) * (-shearFourierFactor) = Complex.sin z := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  unfold shearFourierFactor
  field_simp [Complex.I_ne_zero]
  ring

/-- The two-mode torus field is the complexification of the actual
stationary shear on its Euclidean lift. -/
theorem stationaryShearComplexTorus_lift (s : ℝ) (x : Vec3) :
    stationaryShearComplexTorus s (toUnitTorus x) = periodicComplexifyVector (stationaryShear s x) := by
  classical
  have hnot : stationaryShearMode ∉ ({-stationaryShearMode} : Finset _) := by
    simpa only [Finset.mem_singleton] using stationaryShearMode_ne_neg
  obtain ⟨hp, hm⟩ := fourierMode_shear_signed x
  have hpos : stationaryShearFourierCoeff s stationaryShearMode =
      shearFourierFactor • shearFourierDirection s := by
    rw [stationaryShearFourierCoeff, ite_eq_left rfl]
  have hneg : stationaryShearFourierCoeff s (-stationaryShearMode) =
      (-shearFourierFactor) • shearFourierDirection s := by
    rw [stationaryShearFourierCoeff, ite_eq_right (Ne.symm stationaryShearMode_ne_neg),
      ite_eq_left rfl]
  unfold stationaryShearComplexTorus finiteFourierSum
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp only [hpos, hneg, smul_smul, ← add_smul]
  rw [← fourierMode, ← fourierMode, hp, hm, sine_from_signed_modes, ← Complex.ofReal_sin]
  change ((Real.sin (2 * Real.pi * x 1) : ℝ) : ℂ) • shearFourierDirection s =
    periodicComplexifyVector (Real.sin (2 * Real.pi * x 1) •
      ((EuclideanSpace.single 0 1 : Vec3) + s • EuclideanSpace.single 2 1))
  apply PiLp.ext
  intro i
  simp [shearFourierDirection, PiLp.smul_apply, smul_eq_mul]

theorem stationaryShear_mFourierCoeff (s : ℝ) (k : Fin 3 → ℤ) :
    mFourierCoeff (stationaryShearComplexTorus s) k = stationaryShearFourierCoeff s k := by
  classical
  unfold stationaryShearComplexTorus
  rw [mFourierCoeff_finiteFourierSum]
  by_cases hp : k = stationaryShearMode
  · simp [hp]
  by_cases hm : k = -stationaryShearMode
  · simp [hm]
  · simp [hp, hm, stationaryShearFourierCoeff]

/-- The Fourier support is exactly the two signed second-coordinate modes. -/
theorem stationaryShear_mFourierCoeff_ne_zero_iff (s : ℝ) (k : Fin 3 → ℤ) :
    mFourierCoeff (stationaryShearComplexTorus s) k ≠ 0 ↔
      k = stationaryShearMode ∨ k = -stationaryShearMode := by
  classical
  rw [stationaryShear_mFourierCoeff]
  by_cases hp : k = stationaryShearMode
  · rw [stationaryShearFourierCoeff, ite_eq_left hp]
    exact iff_of_true (smul_ne_zero shearFourierFactor_ne_zero (shearFourierDirection_ne_zero s))
      (Or.inl hp)
  by_cases hm : k = -stationaryShearMode
  · rw [stationaryShearFourierCoeff, ite_eq_right hp, ite_eq_left hm]
    exact iff_of_true
      (smul_ne_zero (neg_ne_zero.mpr shearFourierFactor_ne_zero) (shearFourierDirection_ne_zero s))
      (Or.inr hm)
  · simp [stationaryShearFourierCoeff, hp, hm]

private theorem norm_latticeVector_stationaryShearMode : ‖latticeVector stationaryShearMode‖ = 1 := by
  have h : latticeVector stationaryShearMode = EuclideanSpace.single 1 (1 : ℝ) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> norm_num [latticeVector, stationaryShearMode,
      Fin.zero_eta, Fin.mk_one]
  rw [h]
  simp [EuclideanSpace.single, PiLp.norm_single]

/-- The actual explicit shear gives a two-time label flow on the whole
closed slab. -/
theorem stationaryShear_isLabelFlowOn (s : ℝ) (J : Set ℝ) :
    IsLabelFlowOn (fun _ => stationaryShear s) (fun r t => stationaryShearFlow s (t - r)) J where
  initial r _ a := by simp [stationaryShearFlow]
  trajectory r _ a t _ := by
    have h := (hasDerivAt_stationaryShearFlow s (t - r) a).scomp t
      ((hasDerivAt_id t).sub_const r)
    simpa only [Function.comp_def, id_eq, one_smul] using h.hasDerivWithinAt (s := J)

theorem stationaryShearFlow_lattice_equiv (s t : ℝ) (n : Fin 3 → ℤ) (a : Vec3) :
    stationaryShearFlow s t (a + latticeVector n) =
      stationaryShearFlow s t a + latticeVector n := by
  simp only [stationaryShearFlow, spatiallyPeriodic_stationaryShear s n a]
  abel

theorem odd_stationaryShearFlow (s t : ℝ) : Function.Odd (stationaryShearFlow s t) := by
  intro a
  simp only [stationaryShearFlow, odd_stationaryShear s a, smul_neg, neg_add]

/-- The Jacobian of the inverse flow at the particle and the forward label
Jacobian are the two explicit maps in (6.2). -/
theorem stationaryShearFlow_jacobians_eq (s t : ℝ) (a : Vec3) :
    let F := fderiv ℝ (stationaryShearFlow s t) a
    let G := fderiv ℝ (stationaryShearFlow s (-t)) (stationaryShearFlow s t a)
    let c := t * Real.cos (2 * Real.pi * a 1)
    F = ContinuousLinearMap.id ℝ Vec3 + c • stationaryShearGradient s ∧
      G = ContinuousLinearMap.id ℝ Vec3 - c • stationaryShearGradient s := by
  dsimp only
  refine ⟨(hasFDerivAt_stationaryShearFlow s t a).fderiv, ?_⟩
  rw [(hasFDerivAt_stationaryShearFlow s (-t) (stationaryShearFlow s t a)).fderiv,
    stationaryShearFlow_second]
  apply ContinuousLinearMap.ext
  intro y
  change y + ((-t) * Real.cos (2 * Real.pi * a 1)) • (stationaryShearGradient s) y =
    y - (t * Real.cos (2 * Real.pi * a 1)) • (stationaryShearGradient s) y
  rw [sub_eq_add_neg, neg_mul, _root_.neg_smul]

theorem stationaryShearFlow_jacobians_inverse (s t : ℝ) (a : Vec3) :
    let F := fderiv ℝ (stationaryShearFlow s t) a
    let G := fderiv ℝ (stationaryShearFlow s (-t)) (stationaryShearFlow s t a)
    F.comp G = ContinuousLinearMap.id ℝ Vec3 ∧ G.comp F = ContinuousLinearMap.id ℝ Vec3 := by
  obtain ⟨hF, hG⟩ := stationaryShearFlow_jacobians_eq s t a
  dsimp only
  rw [hF, hG]
  exact stationaryShearDeformation_inverse s (t * Real.cos (2 * Real.pi * a 1))

/-- Both actual Jacobians have norm at most `1 + 4π` for `S₀=1`. -/
theorem stationaryShearFlow_jacobian_norms {s t : ℝ} (hs : |s| ≤ 1) (ht : t ∈ Icc 0 1)
    (a : Vec3) :
    ‖fderiv ℝ (stationaryShearFlow s t) a‖ ≤ 1 + 4 * Real.pi ∧
      ‖fderiv ℝ (stationaryShearFlow s (-t)) (stationaryShearFlow s t a)‖ ≤ 1 + 4 * Real.pi := by
  obtain ⟨hF, hG⟩ := stationaryShearFlow_jacobians_eq s t a
  let c := t * Real.cos (2 * Real.pi * a 1)
  have hcos : |Real.cos (2 * Real.pi * a 1)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hc : |c| ≤ 1 := by
    unfold c
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul ht.2 hcos (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hD : ‖c • stationaryShearGradient s‖ ≤ 4 * Real.pi := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hc (norm_stationaryShearGradient_le hs) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  rw [hF, hG]
  exact ⟨(norm_add_le _ _).trans (add_le_add norm_id_le hD),
    (norm_sub_le _ _).trans (add_le_add norm_id_le hD)⟩

private theorem stationaryShear_gradient_square (s : ℝ) (x : Vec3) :
    (fderiv ℝ (stationaryShear s) x).comp (fderiv ℝ (stationaryShear s) x) = 0 := by
  rw [(hasFDerivAt_stationaryShear s x).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  have hB : (stationaryShearGradient s) ((stationaryShearGradient s) v) = 0 := by
    simpa only [comp_apply, zero_apply] using DFunLike.congr_fun (stationaryShearGradient_sq s) v
  simp only [comp_apply, smul_apply, map_smul, hB, smul_zero, zero_apply]

/-- Zero pressure is mean-zero and solves the parent's Poisson equation
at every point, since the velocity gradient is square-zero. -/
theorem stationaryShear_normalized_pressure (s : ℝ) :
    ((∫ _ in centeredCell, (0 : ℝ)) = 0) ∧
      ∀ x, divergence (gradient (fun _ : Vec3 => (0 : ℝ))) x =
        -LinearMap.trace ℝ Vec3
          ((fderiv ℝ (stationaryShear s) x).comp (fderiv ℝ (stationaryShear s) x)).toLinearMap := by
  refine ⟨by simp, fun x => ?_⟩
  simp [stationaryShear_gradient_square, divergence]

/-- The parent's residual vanishes on the closed slab, including its
one-sided derivative at activation. -/
theorem stationaryShear_closed_residual (s t : ℝ) (x : Vec3) :
    derivWithin (fun _ : ℝ => stationaryShear s x) (Icc 0 1) t +
        fderiv ℝ (stationaryShear s) x (stationaryShear s x) +
        gradient (fun _ : Vec3 => (0 : ℝ)) x = 0 := by
  simp [stationaryShear_advection]

/-- (T1) at index zero, using `S₀=1` and `Λ₀ = λ₀^5`. -/
theorem stationaryShear_base_T1 {s freq₀ : ℝ} (hfreq₀ : 1 ≤ freq₀) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun _ : ℝ => stationaryShear s))
      (Icc 0 1 ×ˢ (univ : Set Vec3)) ∧
    SpatiallyPeriodic (stationaryShear s) ∧ Function.Odd (stationaryShear s) ∧
    (∀ x, divergence (stationaryShear s) x = 0) ∧
    ∀ k ∉ frequencyBand (2 * freq₀ ^ 5), mFourierCoeff (stationaryShearComplexTorus s) k = 0 := by
  have hEuler := isEulerSolution_stationaryShear s (T := 2) (by norm_num)
  have hband : stationaryShearMode ∈ frequencyBand (2 * freq₀ ^ 5) := by
    rw [mem_frequencyBand, norm_latticeVector_stationaryShearMode]
    have hpow : 1 ≤ freq₀ ^ 5 := one_le_pow₀ hfreq₀
    linarith only [hpow]
  refine ⟨hEuler.smooth_velocity.mono ?_, spatiallyPeriodic_stationaryShear s,
    odd_stationaryShear s, divergence_stationaryShear s, fun k hk => ?_⟩
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, ht.2.trans_lt (by norm_num)⟩, hx⟩
  · by_contra hnonzero
    rcases (stationaryShear_mFourierCoeff_ne_zero_iff s k).mp hnonzero with rfl | rfl
    · exact hk hband
    · exact hk ((mem_frequencyBand_neg _ _).mpr hband)

theorem torusLInf_stationaryShear_le_two {s : ℝ} (hs : |s| ≤ 1) :
    torusLInf (stationaryShear s) ≤ ENNReal.ofReal 2 := by
  exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall (norm_stationaryShear_le hs))

/-- (T2) at index zero. The time-independent velocity obeys the
essential-supremum bound, both Jacobians obey the operator-norm bound, and
the actual momentum residual is zero on the full closed slab. -/
theorem stationaryShear_base_T2 {s freq₀ freq₁ : ℝ} (hs : |s| ≤ 1)
    (hfreq₀ : 1 + 4 * Real.pi ≤ freq₀) :
    torusLInf (stationaryShear s) ≤ ENNReal.ofReal freq₀ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ a : Vec3,
      ‖fderiv ℝ (stationaryShearFlow s t) a‖ ≤ freq₀ ∧
        ‖fderiv ℝ (stationaryShearFlow s (-t)) (stationaryShearFlow s t a)‖ ≤ freq₀) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      torusLInf (fun x => derivWithin (fun _ : ℝ => stationaryShear s x) (Icc 0 1) t +
        fderiv ℝ (stationaryShear s) x (stationaryShear s x) +
        gradient (fun _ : Vec3 => (0 : ℝ)) x) ≤ ENNReal.ofReal (freq₁ ^ (-3 : ℤ)) := by
  have htwo : 2 ≤ freq₀ := by linarith only [hfreq₀, Real.pi_gt_three]
  refine ⟨(torusLInf_stationaryShear_le_two hs).trans (ENNReal.ofReal_le_ofReal htwo),
    fun t ht a => ?_, fun t _ => ?_⟩
  · obtain ⟨hF, hG⟩ := stationaryShearFlow_jacobian_norms hs ht a
    exact ⟨hF.trans hfreq₀, hG.trans hfreq₀⟩
  · have hR := funext (stationaryShear_closed_residual s t)
    rw [hR]
    change torusLInf (0 : Vec3 → Vec3) ≤ _
    rw [torusLInf, eLpNormEssSup_zero]
    exact bot_le

/-- (T3) at index zero, where the sum of the Hessian budgets is empty. -/
theorem stationaryShear_base_T3 (x : Vec3) :
    fderiv ℝ (gradient (fun _ : Vec3 => (0 : ℝ))) x = 0 := by simp

private theorem radialEnvelope_zero_collar {r : ℝ} (hr : 0 < r) (a : Vec3)
    (ha : ∃ i : Fin 3, 1 / 2 - (1 / 2 - 2 * r) < |a i|) :
    radialEnvelope r a = 0 := by
  obtain ⟨i, hi⟩ := ha
  apply radialEnvelope_eq_zero hr
  have hnorm : |a i| ≤ ‖a‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a i
  linarith only [hi, hnorm]

private theorem small_ball_mem_interior_centeredCell {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball (0 : Vec3) r ⊆ interior centeredCell := by
  apply Metric.isOpen_ball.subset_interior_iff.mpr
  intro x hx i
  have hnorm : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hx' : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  exact abs_le.mp (hnorm.trans ((hx'.le).trans hr))

/-- At activation, the collar envelope and the exact periodic phase
primitive give a divergence-free curl completion. On the inner ball it
agrees with the plane wave, so the central gradient is exactly `b ⊗ k`. -/
theorem initialLocalizedCompletedWave_properties {r h : ℝ} {k b : Vec3}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hk : k ≠ 0) (hb : ⟪k, b⟫_ℝ = 0) :
    let g := radialEnvelope r
    let C := (-(‖k‖ ^ 2)⁻¹) • cross3 k b
    let W := curl (periodizeCentered (fun a => (g a * wavePressurePrimitive h ⟪k, a⟫_ℝ) • C))
    ContDiff ℝ ∞ W ∧ SpatiallyPeriodic W ∧ (∀ x, divergence W x = 0) ∧
      EqOn W (fun a => waveProfile h ⟪k, a⟫_ℝ • b) (Metric.ball 0 r) ∧
      HasFDerivAt W ((innerSL ℝ k).smulRight b) 0 := by
  let g := radialEnvelope r
  let C := (-(‖k‖ ^ 2)⁻¹) • cross3 k b
  let δ := 1 / 2 - 2 * r
  let A : Velocity := fun _ => id
  let Q : ℝ → Vec3 → ℝ → Vec3 := fun _ a q => (g a * wavePressurePrimitive h q) • C
  let W := curl (localizedTransportedProfile A k Q 0)
  have hreg : ContDiff ℝ ∞ (fun a => Q 0 a ⟪k, a⟫_ℝ) := by
    exact ((contDiff_radialEnvelope hr).mul
      ((contDiff_wavePressurePrimitive hh hh₁).comp (innerSL ℝ k).contDiff)).smul contDiff_const
  have hzero a (ha : ∃ i : Fin 3, 1 / 2 - δ < |a i|) : Q 0 a ⟪k, a⟫_ℝ = 0 := by
    simp only [Q, g, radialEnvelope_zero_collar hr a ha, zero_mul, zero_smul]
  obtain ⟨hW, hper, hsol, hloc⟩ := localizedCurl_properties (A := A) (k := k) (t := 0) (Q := Q)
    (by exact contDiff_id) (fun _ _ => rfl) (by dsimp only [δ]; linarith)
    (by dsimp only [δ]; linarith) hreg hzero
  have hEq : EqOn W (fun a => waveProfile h ⟪k, a⟫_ℝ • b) (Metric.ball 0 r) := by
    intro x hx
    have hxcell : x ∈ interior centeredCell :=
      small_ball_mem_interior_centeredCell (by linarith only [hcell, hr]) hx
    have hNear : transportedProfile A k Q 0 =ᶠ[nhds x]
        fun a => wavePressurePrimitive h ⟪k, a⟫_ℝ • C := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with a ha
      have hb : ‖a‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using ha
      simp only [transportedProfile, A, Q, id_eq, g, radialEnvelope_eq_one hr hb.le, one_mul]
    calc
      W x = curl (transportedProfile A k Q 0) x := hloc x hxcell
      _ = curl (fun a => wavePressurePrimitive h ⟪k, a⟫_ℝ • C) x :=
        congrArg curlOfDerivative hNear.fderiv_eq
      _ = waveProfile h ⟪k, x⟫_ℝ • cross3 k C :=
        curl_planeWave _ _ _ _ _ (hasDerivAt_wavePressurePrimitive hh hh₁ _)
      _ = _ := by rw [show cross3 k C = b from cross3_neg_inv_norm_sq_smul hk hb]
  have hDeriv := (hasFDerivAt_planeWave (waveProfile h) b k 0 1
    (by simpa only [inner_zero_right] using hasDerivAt_waveProfile_zero hh hh₁))
  rw [one_smul] at hDeriv
  refine ⟨hW, hper, hsol, hEq, hDeriv.congr_of_eventuallyEq ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Vec3) hr] with x hx using hEq hx

end
end TorusEuler
