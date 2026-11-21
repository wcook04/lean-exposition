import TorusEuler.FirstWaveInitialization

/-! # The first wave (6.3) exists: an explicit solution at the origin

The setting of Lemma 6.1 (sections/03a_exact_base.tex:19-27) takes the first wave of frequency
`λ` over the shear (6.1): `κ(0,0) = λe_1`, and at the origin the seed equation (3.2) is solved
with initial direction `e_2` and scaled so that `max_{[0,T]} |𝐚(t,0)| = λ^{-3/4}`. Over the
constant gradient `B_ρ = 2π(e_1 + ρe_3) ⊗ e_2` both equations are solved in closed form:
with `g(t) = (1 + 4π²t²)^{-1}`,
`κ(t,0) = λ(e_1 - 2πt e_2)` and `𝐚(t,0) ∝ g(t)(2πt e_1 + e_2) - ρ arctan(2πt) e_3`.
The pair is perpendicular (`κ·𝐚 = 0` identically) and both vectors are nonzero (first,
respectively second, coordinate). This file verifies these formulas and rescales the amplitude
to the prescribed peak, which constructs a `FirstWaveOrigin ρ T λ` for every `T ≥ 0`, `λ > 0`.
The argument checks the explicit solution directly; it does not use the persistence of
transversality (Lemma 2.1) nor the library existence lemma `firstWaveOrigin_exists`. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S678b

noncomputable section

/-- The coordinate vector `e_{i+1}` of `ℝ³` (indices from `0`). -/
abbrev unitAxis (i : Fin 3) : Vec3 := EuclideanSpace.single i 1

/-- The gradient `B_ρ x = 2π x_2 (e_1 + ρe_3)` of (6.1), in coordinates. -/
theorem stationaryShearGradient_apply' (s : ℝ) (x : Vec3) :
    stationaryShearGradient s x =
      (2 * Real.pi * x 1) • (unitAxis 0 + s • unitAxis 2) := by
  have h : stationaryShearGradient s x = (2 * Real.pi) •
      (⟪(EuclideanSpace.single 1 1 : Vec3), x⟫_ℝ • (unitAxis 0 + s • unitAxis 2)) := rfl
  rw [h, smul_smul, EuclideanSpace.inner_single_left]
  congr 1
  simp

/-- The adjoint of `B_ρ`: `B_ρ^T y = 2π ((e_1 + ρe_3)·y) e_2`. -/
theorem stationaryShearGradient_adjoint_apply (s : ℝ) (y : Vec3) :
    (stationaryShearGradient s).adjoint y =
      (2 * Real.pi * ⟪unitAxis 0 + s • unitAxis 2, y⟫_ℝ) • unitAxis 1 := by
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right, stationaryShearGradient_apply',
    real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_right]
  simp only [conj_trivial]
  ring

/-- The scalar factor `g(t) = (1 + 4π²t²)^{-1}`. -/
def firstWaveGauge (t : ℝ) : ℝ := (1 + (2 * Real.pi * t) ^ 2)⁻¹

/-- `g(t) > 0`. -/
theorem firstWaveGauge_pos (t : ℝ) : 0 < firstWaveGauge t := by
  unfold firstWaveGauge
  positivity

/-- The explicit wave vector `κ(t,0) = λ(e_1 - 2πt e_2)` of the first wave at the origin. -/
def firstWaveCovector (freq t : ℝ) : Vec3 :=
  freq • (unitAxis 0 - (2 * Real.pi * t) • unitAxis 1)

/-- The explicit unnormalized seed `g(t)(2πt e_1 + e_2) - ρ arctan(2πt) e_3` at the origin. -/
def firstWaveSeed (s t : ℝ) : Vec3 :=
  (2 * Real.pi * t * firstWaveGauge t) • unitAxis 0 + firstWaveGauge t • unitAxis 1 +
    (-(s * Real.arctan (2 * Real.pi * t))) • unitAxis 2

/-- Coordinates of the explicit wave vector `λ(e_1 - 2πt e_2)`. -/
@[simp] theorem firstWaveCovector_apply (freq t : ℝ) (i : Fin 3) :
    firstWaveCovector freq t i =
      freq * ((if i = 0 then 1 else 0) - 2 * Real.pi * t * (if i = 1 then 1 else 0)) := by
  fin_cases i <;> simp [firstWaveCovector, unitAxis]

/-- Coordinates of the explicit seed. -/
@[simp] theorem firstWaveSeed_apply (s t : ℝ) (i : Fin 3) :
    firstWaveSeed s t i =
      2 * Real.pi * t * firstWaveGauge t * (if i = 0 then 1 else 0) +
        firstWaveGauge t * (if i = 1 then 1 else 0) +
        -(s * Real.arctan (2 * Real.pi * t)) * (if i = 2 then 1 else 0) := by
  fin_cases i <;> simp [firstWaveSeed, unitAxis]

/-- The inner product of `ℝ³` in coordinates. -/
theorem inner_vec3 (x y : Vec3) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- The squared norm of `ℝ³` in coordinates. -/
theorem norm_sq_vec3 (x : Vec3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vec3]
  ring

/-- The explicit pair is perpendicular: `κ·𝐚 = λ(2πt g - 2πt g) = 0`. -/
theorem firstWaveCovector_inner_seed (freq s t : ℝ) :
    ⟪firstWaveCovector freq t, firstWaveSeed s t⟫_ℝ = 0 := by
  rw [inner_vec3]
  simp
  ring

/-- The explicit wave vector is nonzero (first coordinate `λ`). -/
theorem firstWaveCovector_ne_zero {freq : ℝ} (hf : 0 < freq) (t : ℝ) :
    firstWaveCovector freq t ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Vec3 => v 0) h
  simp at h0
  exact hf.ne' h0

/-- The explicit seed is nonzero (second coordinate `g(t) > 0`). -/
theorem firstWaveSeed_ne_zero (s t : ℝ) : firstWaveSeed s t ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Vec3 => v 1) h
  simp at h1
  exact (firstWaveGauge_pos t).ne' h1

/-- The wave vector equation `κ' = -B_ρ^Tκ` at the origin. -/
theorem hasDerivAt_firstWaveCovector (s freq t : ℝ) :
    HasDerivAt (firstWaveCovector freq)
      (-((stationaryShearGradient s).adjoint (firstWaveCovector freq t))) t := by
  have h1 : HasDerivAt (fun r : ℝ => (2 * Real.pi * r) • unitAxis 1)
      ((2 * Real.pi * 1) • unitAxis 1) t :=
    ((hasDerivAt_id t).const_mul (2 * Real.pi)).smul_const (unitAxis 1)
  have h2 := (h1.const_sub (unitAxis 0)).const_smul freq
  refine h2.congr_deriv ?_
  rw [stationaryShearGradient_adjoint_apply, inner_vec3]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [unitAxis]
  ring

/-- The seed equation `𝐚' = -B_ρ𝐚 + 2(κ·B_ρ𝐚/|κ|²)κ` (3.2) at the origin. -/
theorem hasDerivAt_firstWaveSeed (s : ℝ) {freq : ℝ} (hf : 0 < freq) (t : ℝ) :
    HasDerivAt (firstWaveSeed s)
      (affineWaveAmplitudeOperator (stationaryShearGradient s) (firstWaveCovector freq t)
        (firstWaveSeed s t)) t := by
  set c := 2 * Real.pi with hc
  have hq := (((hasDerivAt_id' t).const_mul c).pow 2).const_add 1
  have hq0 : 1 + (c * t) ^ 2 ≠ 0 := by positivity
  have hg : HasDerivAt firstWaveGauge _ t := hq.inv hq0
  have hf0 := ((hasDerivAt_id' t).const_mul c).mul hg
  have hat := (((hasDerivAt_id' t).const_mul c).arctan.const_mul s).neg
  have hd := ((hf0.smul_const (unitAxis 0)).add (hg.smul_const (unitAxis 1))).add
    (hat.smul_const (unitAxis 2))
  refine hd.congr_deriv ?_
  rw [affineWaveAmplitudeOperator_apply, norm_sq_vec3, inner_vec3, stationaryShearGradient_apply']
  have hgt : firstWaveGauge t = (1 + (c * t) ^ 2)⁻¹ := rfl
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [unitAxis, hgt, ← hc] <;> field_simp
  ring

/-- The first wave (6.3) at the origin exists on `[0,T]` for every `T ≥ 0` and `λ > 0`
(sections/03a_exact_base.tex:19-27): the explicit pair `(firstWaveCovector λ, c·firstWaveSeed ρ)`
solves (2.1) and the seed equation (3.2) over `B_ρ` with `κ(0,0) = λe_1`, initial direction
`e_2`, stays perpendicular and nonzero, and the factor `c > 0` makes the maximum of `|𝐚(t,0)|`
over `[0,T]` (attained, by compactness) equal to `λ^{-3/4}`. -/
theorem firstWaveOrigin_exists_explicit {s T freq : ℝ} (hT : 0 ≤ T) (hf : 0 < freq) :
    Nonempty (FirstWaveOrigin s T freq) := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  let a := firstWaveSeed s
  have ha_cont : Continuous a := continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_firstWaveSeed s hf t).continuousAt
  have hnormc : ContinuousOn (fun t => ‖a t‖) (Icc 0 T) := ha_cont.norm.continuousOn
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, h0T⟩ hnormc
  have hM : 0 < ‖a tmax‖ := norm_pos_iff.mpr (firstWaveSeed_ne_zero s tmax)
  let c : ℝ := freq ^ (-(3 / 4) : ℝ) / ‖a tmax‖
  have hc : 0 < c := div_pos (Real.rpow_pos_of_pos hf _) hM
  have hpeak (t : ℝ) : ‖c • a t‖ = c * ‖a t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hcm : c * ‖a tmax‖ = freq ^ (-(3 / 4) : ℝ) := div_mul_cancel₀ _ hM.ne'
  have ha0 : a 0 = EuclideanSpace.single 1 1 := by
    simp [a, firstWaveSeed, firstWaveGauge, unitAxis]
  refine ⟨⟨firstWaveCovector freq, fun t => c • a t, c, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [firstWaveCovector, unitAxis]
  · simp only [ha0]
  · intro t _
    exact (hasDerivAt_firstWaveCovector s freq t).hasDerivWithinAt
  · intro t _
    have h := ((hasDerivAt_firstWaveSeed s hf t).hasDerivWithinAt (s := Icc 0 T)).const_smul c
    rw [← map_smul] at h
    exact h
  · intro t _
    exact ⟨firstWaveCovector_ne_zero hf t, smul_ne_zero hc.ne' (firstWaveSeed_ne_zero s t), by
      rw [real_inner_smul_right, firstWaveCovector_inner_seed, mul_zero]⟩
  · intro t ht
    rw [hpeak, ← hcm]
    exact mul_le_mul_of_nonneg_left (hmax ht) hc.le
  · exact ⟨tmax, htmax, (hpeak tmax).trans hcm⟩

end

end TorusEuler.Paper.Lib.S678b
