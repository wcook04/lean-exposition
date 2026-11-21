import TorusEuler.EndpointMomentum
import TorusEuler.EndpointWeakInstantaneous
import TorusEuler.EulerAdvectionBounds
import TorusEuler.FourierCutoffBounds
import TorusEuler.PeriodicLerayReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Recovery of the scalar pressure from the nullspace of the spatial Leray projection. -/

open Filter MeasureTheory MeasureTheory.Measure Set UnitAddTorus
open scoped ContDiff InnerProductSpace SchwartzMap Topology

namespace TorusEuler

local notation "A" => UnitAddTorus (Fin 3)
local notation "H" => Lp Vec3 2 unitTorusMeasure

noncomputable section

noncomputable section

private theorem cutoffUniform_integral_dilation {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Λ : ℝ} (hΛ : 0 < Λ) (f : Vec3 → F) :
    (∫ y : Vec3, Λ ^ 3 • f (Λ • y)) = ∫ y, f y := by
  rw [integral_smul, integral_comp_smul_of_nonneg volume f Λ (hR := hΛ.le),
    finrank_euclideanSpace_fin, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hΛ.ne'), one_smul]

private theorem cutoffUniform_continuous_toUnitTorus : Continuous toUnitTorus :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)

variable {E : Type*} [NormedAddCommGroup E]

private def cutoffUniform_shift (g : C(UnitAddTorus (Fin 3), E)) (y : Vec3) :
    C(UnitAddTorus (Fin 3), E) :=
  ⟨fun z => g (z - toUnitTorus y), g.continuous.comp (continuous_id.sub continuous_const)⟩

private theorem cutoffUniform_continuous_shift (g : C(UnitAddTorus (Fin 3), E)) :
    Continuous (cutoffUniform_shift g) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (g.continuous.comp (continuous_snd.sub (cutoffUniform_continuous_toUnitTorus.comp continuous_fst)))

private theorem cutoffUniform_shift_zero (g : C(UnitAddTorus (Fin 3), E)) :
    cutoffUniform_shift g 0 = g := by
  have hq0 : toUnitTorus 0 = 0 := by ext i; simp [toUnitTorus]
  ext z
  change g (z - toUnitTorus 0) = g z
  rw [hq0, sub_zero]

private theorem cutoffUniform_norm_shift_le (g : C(UnitAddTorus (Fin 3), E)) (y : Vec3) :
    ‖cutoffUniform_shift g y‖ ≤ ‖g‖ :=
  (ContinuousMap.norm_le (cutoffUniform_shift g y) (norm_nonneg g)).mpr fun z =>
    g.norm_coe_le_norm (z - toUnitTorus y)

variable [NormedSpace ℂ E]

private theorem cutoffUniform_integrable_shift (g : C(UnitAddTorus (Fin 3), E))
    {K : Vec3 → ℂ} (hc : Continuous K) (hK : Integrable K) (a : ℝ) :
    Integrable (fun y => K y • cutoffUniform_shift g (a • y)) := by
  have hscale : Continuous (fun y : Vec3 => a • y) := continuous_const_smul a
  have hshift : Continuous (fun y : Vec3 => cutoffUniform_shift g (a • y)) :=
    (cutoffUniform_continuous_shift g).comp hscale
  have hmeas : AEStronglyMeasurable (fun y : Vec3 => K y • cutoffUniform_shift g (a • y))
      volume := (hc.smul hshift).aestronglyMeasurable
  apply (hK.norm.mul_const ‖g‖).mono' hmeas
  filter_upwards with y
  change ‖K y • cutoffUniform_shift g (a • y)‖ ≤ ‖K y‖ * ‖g‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (cutoffUniform_norm_shift_le g _) (norm_nonneg _)

variable [CompleteSpace E]

private theorem cutoffUniform_integral_tendsto (g : C(UnitAddTorus (Fin 3), E))
    {K : Vec3 → ℂ} (hc : Continuous K) (hK : Integrable K)
    (hMass : (∫ y, K y) = (1 : ℂ)) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, K y • cutoffUniform_shift g (a n • y)) atTop (𝓝 g) := by
  let F (n : ℕ) (y : Vec3) : C(UnitAddTorus (Fin 3), E) :=
    K y • cutoffUniform_shift g (a n • y)
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (cutoffUniform_integrable_shift g hc hK (a n)).aestronglyMeasurable
  have hdom (n : ℕ) : ∀ᵐ y ∂(volume : Measure Vec3), ‖F n y‖ ≤ ‖K y‖ * ‖g‖ :=
    ae_of_all _ fun y => by
      change ‖K y • cutoffUniform_shift g (a n • y)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (cutoffUniform_norm_shift_le g _) (norm_nonneg _)
  have hLim (y : Vec3) : Tendsto (fun n => F n y) atTop (𝓝 (K y • g)) := by
    have h := ((cutoffUniform_continuous_shift g).continuousAt.tendsto.comp
      (ha.smul_const y)).const_smul (K y)
    simpa only [F, Function.comp_apply, zero_smul, cutoffUniform_shift_zero] using h
  have h := tendsto_integral_of_dominated_convergence
    (F := F) (f := fun y => K y • g) (fun y => ‖K y‖ * ‖g‖)
    hMeas (hK.norm.mul_const ‖g‖) hdom (ae_of_all _ hLim)
  rw [integral_smul_const, hMass, one_smul] at h
  exact h

private theorem cutoffUniform_evaluate_dilation {K : Vec3 → ℂ} (hc : Continuous K)
    (hK : Integrable K) (g : C(UnitAddTorus (Fin 3), E)) {Λ : ℝ} (hΛ : 0 < Λ)
    (x : Vec3) :
    (∫ y, K y • cutoffUniform_shift g (Λ⁻¹ • y)) (toUnitTorus x) =
      liftConvolution (scaledLiftKernel Λ K) (fun z => g (toUnitTorus z)) x := by
  let ev : C(UnitAddTorus (Fin 3), E) →L[ℂ] E := ContinuousMap.evalCLM ℂ (toUnitTorus x)
  have hi := ev.integral_comp_comm (cutoffUniform_integrable_shift g hc hK Λ⁻¹)
  change (∫ y, K y • g (toUnitTorus x - toUnitTorus (Λ⁻¹ • y))) =
    (∫ y, K y • cutoffUniform_shift g (Λ⁻¹ • y)) (toUnitTorus x) at hi
  calc
    _ = ∫ y, K y • g (toUnitTorus x - toUnitTorus (Λ⁻¹ • y)) := hi.symm
    _ = ∫ y : Vec3, Λ ^ 3 • (K (Λ • y) • g
        (toUnitTorus x - toUnitTorus (Λ⁻¹ • (Λ • y)))) :=
      (cutoffUniform_integral_dilation hΛ
        (fun y => K y • g (toUnitTorus x - toUnitTorus (Λ⁻¹ • y)))).symm
    _ = _ := by
      unfold liftConvolution
      apply integral_congr_ae
      filter_upwards with y
      have hsub : toUnitTorus (x - y) = toUnitTorus x - toUnitTorus y := by
        funext i
        exact AddCircle.coe_sub 1 (x i) (y i)
      change Λ ^ 3 • (K (Λ • y) • g
        (toUnitTorus x - toUnitTorus (Λ⁻¹ • (Λ • y)))) =
        scaledLiftKernel Λ K y • g (toUnitTorus (x - y))
      rw [smul_smul Λ⁻¹ Λ y, inv_mul_cancel₀ hΛ.ne', one_smul, hsub, scaledLiftKernel, smul_assoc]

/-- Smooth spectral cutoffs converge uniformly on the periodic lift of every
continuous torus field. -/
theorem tendstoUniformly_lift_smoothFourierCutoff
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ψ 0 = 1) (g : C(UnitAddTorus (Fin 3), E)) :
    TendstoUniformly (fun n : ℕ => fun x : Vec3 =>
      smoothFourierCutoff ψ ((n : ℝ) + 1) g (toUnitTorus x))
      (fun x : Vec3 => g (toUnitTorus x)) atTop := by
  let K : 𝓢(Vec3, ℂ) := cutoffSchwartzKernel hψ hs
  let Λ (n : ℕ) : ℝ := (n : ℝ) + 1
  have hΛ (n : ℕ) : 0 < Λ n := by dsimp [Λ]; positivity
  have hInv : Tendsto (fun n => (Λ n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hMass : (∫ y, K y) = (1 : ℂ) := by
    simpa only [scaledLiftKernel, one_pow, one_smul, hunit, Complex.ofReal_one, K] using
      integral_scaledCutoffSchwartzKernel hψ hs (Λ := 1) zero_lt_one
  let G (n : ℕ) : C(UnitAddTorus (Fin 3), E) :=
    ∫ y, K y • cutoffUniform_shift g ((Λ n)⁻¹ • y)
  have hConv : Tendsto G atTop (𝓝 g) :=
    cutoffUniform_integral_tendsto g K.continuous K.integrable hMass hInv
  have hEval (n : ℕ) (x : Vec3) :
      G n (toUnitTorus x) = smoothFourierCutoff ψ (Λ n) g (toUnitTorus x) :=
    (cutoffUniform_evaluate_dilation K.continuous K.integrable g (hΛ n) x).trans
      (liftConvolution_cutoffSchwartzKernel hψ hs (hΛ n) g x)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hEv := (Metric.tendsto_nhds.mp hConv) ε hε
  filter_upwards [hEv] with n hn x
  change dist (g (toUnitTorus x)) (smoothFourierCutoff ψ (Λ n) g (toUnitTorus x)) < ε
  rw [← hEval, dist_comm, dist_eq_norm]
  exact (ContinuousMap.norm_coe_le_norm (G n - g) (toUnitTorus x)).trans_lt
    (by simpa only [dist_eq_norm] using hn)

end

/-- The continuous torus field with the same real coordinates, regarded as complex. -/
def endpointComplexifyContinuous (g : C(A, Vec3)) : C(A, ComplexEuclideanVec3) :=
  ⟨periodicComplexifyVector ∘ g, periodicComplexifyVector.continuous.comp g.continuous⟩

private theorem endpointComplexifyContinuous_toLp (g : C(A, Vec3)) :
    (endpointComplexifyContinuous g).toLp 2 unitTorusMeasure ℂ =
      periodicComplexifyL2 (g.toLp 2 unitTorusMeasure ℝ) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) unitTorusMeasure
      (endpointComplexifyContinuous g),
    periodicComplexifyL2_apply_ae (g.toLp 2 unitTorusMeasure ℝ),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure g] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

private theorem endpointRealLeray_eq_coe_weakProjection (u : H) :
    periodicRealLeray u = (endpointWeakSpatialProjection u : H) := by
  let : CompleteSpace endpointSpatialSolenoidal := isClosed_endpointSpatialSolenoidal.completeSpace_coe
  rfl

/-- A continuous field killed by the weak spatial projection has longitudinal
complex Fourier coefficients. This includes a vanishing zero coefficient. -/
theorem endpointGradientMode_eq_coeff_of_projection_eq_zero (g : C(A, Vec3))
    (hPg : endpointWeakSpatialProjection (g.toLp 2 unitTorusMeasure ℝ) = 0)
    (k : Fin 3 → ℤ) :
    let a := (mFourierCoeff (endpointComplexifyContinuous g) k).ofLp
    gradientMode k (pressureCorrectionMode k a) = a := by
  let u := g.toLp 2 unitTorusMeasure ℝ
  have h₀ : periodicRealLeray u = 0 := by
    rw [endpointRealLeray_eq_coe_weakProjection, show endpointWeakSpatialProjection u = 0 from hPg]
    rfl
  have h := periodicL2Coefficient_sub_realLeray k u
  have hCoeff : mFourierCoeff ((endpointComplexifyContinuous g).toLp 2 unitTorusMeasure ℂ) k =
      mFourierCoeff (endpointComplexifyContinuous g) k := by
    change (∫ z, mFourier (-k) z • ((endpointComplexifyContinuous g).toLp 2 unitTorusMeasure ℂ) z
      ∂unitTorusMeasure) = ∫ z, mFourier (-k) z • endpointComplexifyContinuous g z ∂unitTorusMeasure
    exact integral_congr_ae
      ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) unitTorusMeasure
        (endpointComplexifyContinuous g)).mono fun z hz =>
          congrArg (fun a : ComplexEuclideanVec3 => mFourier (-k) z • a) hz)
  rw [h₀, sub_zero, ← endpointComplexifyContinuous_toLp, periodicL2Coefficient_eq_mFourierCoeff,
    hCoeff] at h
  exact h.symm

/-- The real pressure of a trigonometric polynomial, with zero constant mode. -/
def endpointFiniteFourierPressure (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexVec3)
    (x : Vec3) : ℝ :=
  (finiteFourierSum s (fun k => pressureCorrectionMode k (a k)) (toUnitTorus x)).re

theorem contDiff_endpointFiniteFourierPressure (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → ComplexVec3) :
    ContDiff ℝ ∞ (endpointFiniteFourierPressure s a) :=
  Complex.reCLM.contDiff.comp (contDiff_lift_finiteFourierSum _ _)

theorem spatiallyPeriodic_endpointFiniteFourierPressure (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → ComplexVec3) :
    SpatiallyPeriodic (endpointFiniteFourierPressure s a) := by
  intro k x
  unfold endpointFiniteFourierPressure
  rw [(toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩]

theorem integral_endpointFiniteFourierPressure (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → ComplexVec3) :
    (∫ x in centeredCell, endpointFiniteFourierPressure s a x) = 0 := by
  let P (x : Vec3) := finiteFourierSum s (fun k => pressureCorrectionMode k (a k)) (toUnitTorus x)
  have hP : IntegrableOn P centeredCell :=
    (contDiff_lift_finiteFourierSum s
      (fun k => pressureCorrectionMode k (a k))).continuous.continuousOn.integrableOn_compact
        isCompact_centeredCell
  change (∫ x in centeredCell, Complex.reCLM (P x)) = 0
  rw [Complex.reCLM.integral_comp_comm hP, show (∫ x in centeredCell, P x) = 0 from
    integral_lift_pressureCorrectionMode s a, map_zero]

/-- The real part of a longitudinal trigonometric polynomial is the gradient
of its real mean-zero Fourier pressure. -/
theorem hasGradientAt_endpointFiniteFourierPressure (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → ComplexEuclideanVec3)
    (ha : ∀ k ∈ s, gradientMode k (pressureCorrectionMode k (a k).ofLp) = (a k).ofLp)
    (x : Vec3) :
    HasGradientAt (endpointFiniteFourierPressure s (fun k => (a k).ofLp))
      (periodicRealPartVector (finiteFourierSum s a (toUnitTorus x))) x := by
  let b (k : Fin 3 → ℤ) := pressureCorrectionMode k (a k).ofLp
  let P (y : Vec3) := finiteFourierSum s b (toUnitTorus y)
  let p := endpointFiniteFourierPressure s (fun k => (a k).ofLp)
  have hP : DifferentiableAt ℝ P x :=
    ((contDiff_lift_finiteFourierSum s b).differentiable (by simp)) x
  have hd := (Complex.reCLM.hasFDerivAt.comp x hP.hasFDerivAt).fderiv
  have hpd : DifferentiableAt ℝ p x :=
    ((contDiff_endpointFiniteFourierPressure s _).differentiable (by simp)) x
  have hgrad : gradient p x = periodicRealPartVector (finiteFourierSum s a (toUnitTorus x)) := by
    apply PiLp.ext
    intro i
    calc
      (gradient p x) i = ⟪gradient p x, EuclideanSpace.single i 1⟫_ℝ := by
        rw [EuclideanSpace.inner_single_right]
        simp
      _ = fderiv ℝ p x (EuclideanSpace.single i 1) := inner_gradient_left
      _ = (complexGradient P x i).re := by
        change fderiv ℝ p x = _ at hd
        rw [hd]
        rfl
      _ = _ := by
        rw [show complexGradient P x = finiteFourierSum s (fun k => gradientMode k (b k))
          (toUnitTorus x) from complexGradient_lift_finiteFourierSum s b x]
        have hsum : finiteFourierSum s (fun k => gradientMode k (b k)) (toUnitTorus x) =
            (finiteFourierSum s a (toUnitTorus x)).ofLp := by
          unfold finiteFourierSum
          have hadd := map_sum (WithLp.addEquiv 2 ComplexVec3)
            (fun k => mFourier k (toUnitTorus x) • a k) s
          change (∑ k ∈ s, mFourier k (toUnitTorus x) • a k).ofLp =
            ∑ k ∈ s, (mFourier k (toUnitTorus x) • a k).ofLp at hadd
          rw [hadd]
          refine Finset.sum_congr rfl fun k hk => ?_
          exact congrArg (fun w : ComplexVec3 => mFourier k (toUnitTorus x) • w) (ha k hk)
        rw [hsum]
        rfl
  change HasGradientAt p _ x
  rw [← hgrad]
  exact hpd.hasGradientAt

private theorem gradientMode_pressureCorrectionMode_real_smul (k : Fin 3 → ℤ)
    (c : ℝ) (a : ComplexVec3) :
    gradientMode k (pressureCorrectionMode k (c • a)) =
      c • gradientMode k (pressureCorrectionMode k a) := by
  unfold pressureCorrectionMode
  rw [divergenceMode_real_smul]
  funext i
  simp only [gradientMode, Complex.real_smul, Pi.smul_apply]
  ring

/-- Every smooth Fourier cutoff of a continuous field in the kernel of the
weak projection has a normalized real pressure on the spatial lift. -/
theorem endpointCutoffPressure_of_projection_eq_zero (g : C(A, Vec3))
    (hPg : endpointWeakSpatialProjection (g.toLp 2 unitTorusMeasure ℝ) = 0)
    (ψ : Vec3 → ℝ) (Λ : ℝ) :
    ∃ p : Vec3 → ℝ, ContDiff ℝ ∞ p ∧ SpatiallyPeriodic p ∧
      (∫ x in centeredCell, p x) = 0 ∧ ∀ x, HasGradientAt p
        (periodicRealPartVector
          (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) (toUnitTorus x))) x := by
  let s := frequencyBand (2 * Λ)
  let a (k : Fin 3 → ℤ) : ComplexEuclideanVec3 :=
    ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff (endpointComplexifyContinuous g) k
  have ha (k : Fin 3 → ℤ) : gradientMode k (pressureCorrectionMode k (a k).ofLp) = (a k).ofLp := by
    change gradientMode k (pressureCorrectionMode k
      (ψ (Λ⁻¹ • latticeVector k) • (mFourierCoeff (endpointComplexifyContinuous g) k).ofLp)) = _
    rw [gradientMode_pressureCorrectionMode_real_smul,
      endpointGradientMode_eq_coeff_of_projection_eq_zero g hPg k]
    rfl
  exact ⟨endpointFiniteFourierPressure s (fun k => (a k).ofLp),
    contDiff_endpointFiniteFourierPressure s _, spatiallyPeriodic_endpointFiniteFourierPressure s _,
    integral_endpointFiniteFourierPressure s _, fun x =>
      hasGradientAt_endpointFiniteFourierPressure s a (fun k _ => ha k) x⟩

/-- Uniform convergence of the real cutoffs of the nullspace field recovers
a mean-zero spatial pressure whose actual gradient is that field. -/
theorem exists_endpointPressure_of_uniformCutoffs (g : C(A, Vec3))
    (hPg : endpointWeakSpatialProjection (g.toLp 2 unitTorusMeasure ℝ) = 0)
    (ψ : Vec3 → ℝ) (Λ : ℕ → ℝ)
    (happrox : TendstoUniformly (fun n x => periodicRealPartVector
      (smoothFourierCutoff ψ (Λ n) (endpointComplexifyContinuous g) (toUnitTorus x)))
      (fun x => g (toUnitTorus x)) atTop) :
    ∃ p : Vec3 → ℝ, SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧
      ∀ x, HasGradientAt p (g (toUnitTorus x)) x := by
  choose p hsmooth hper _ hg using fun n => endpointCutoffPressure_of_projection_eq_zero g hPg ψ (Λ n)
  have hd : ∀ n, Differentiable ℝ (p n) := fun n => (hsmooth n).differentiable (by simp)
  have heq (n : ℕ) : gradient (p n) = fun x => periodicRealPartVector
      (smoothFourierCutoff ψ (Λ n) (endpointComplexifyContinuous g) (toUnitTorus x)) :=
    funext fun x => (hg n x).gradient
  apply exists_periodic_meanZero_pressure_of_uniform_gradient hd hper
  simp_rw [heq]
  exact happrox

/-- A continuous torus field killed by the weak spatial projection is the
actual gradient of a periodic, normalized scalar pressure. -/
theorem exists_endpointPressure_of_projection_eq_zero (g : C(A, Vec3))
    (hPg : endpointWeakSpatialProjection (g.toLp 2 unitTorusMeasure ℝ) = 0) :
    ∃ p : Vec3 → ℝ, SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧
      ∀ x, HasGradientAt p (g (toUnitTorus x)) x := by
  let ψ : ContDiffBump (0 : Vec3) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hψ (ξ : Vec3) (hξ : 2 < ‖ξ‖) : ψ ξ = 0 :=
    ψ.zero_of_le_dist (by simpa only [ψ, dist_zero_right] using hξ.le)
  have hψ0 : ψ 0 = 1 := ψ.one_of_mem_closedBall (by simp [ψ])
  have hre (z : A) : periodicRealPartVector (endpointComplexifyContinuous g z) = g z := by
    apply PiLp.ext
    intro i
    simp only [endpointComplexifyContinuous, ContinuousMap.coe_mk, Function.comp_apply,
      periodicRealPartVector_apply, periodicComplexifyVector_apply, Complex.ofReal_re]
  refine exists_endpointPressure_of_uniformCutoffs g hPg ψ (fun n => (n : ℝ) + 1) ?_
  have h := periodicRealPartVector.uniformContinuous.comp_tendstoUniformly
    (tendstoUniformly_lift_smoothFourierCutoff hψ ψ.contDiff hψ0 (endpointComplexifyContinuous g))
  change TendstoUniformly (fun (n : ℕ) x => periodicRealPartVector
    (smoothFourierCutoff ψ ((n : ℝ) + 1) (endpointComplexifyContinuous g) (toUnitTorus x)))
    (fun x => periodicRealPartVector (endpointComplexifyContinuous g (toUnitTorus x))) atTop at h
  simpa only [hre] using h

/-- Subtracting the solenoidal constant in the integrated equation leaves a
fixed-time residual in the kernel of the spatial Leray projection. -/
theorem endpointProjection_residual_eq_zero (F : HalfHolder A Vec3)
    (c : endpointHalfHolderSolenoidal)
    (hF : endpointWeakSpatialProjection (endpointHalfHolderToL2 F) =
      endpointSolenoidalEmbedding c) :
    endpointWeakSpatialProjection (endpointHalfHolderToL2 (F - (c : HalfHolder A Vec3))) = 0 := by
  have hc : endpointWeakSpatialProjection (endpointHalfHolderToL2 (c : HalfHolder A Vec3)) =
      endpointSolenoidalEmbedding c := by
    let : CompleteSpace endpointSpatialSolenoidal := isClosed_endpointSpatialSolenoidal.completeSpace_coe
    change endpointSpatialSolenoidal.orthogonalProjectionOnto ((endpointSolenoidalEmbedding c : H)) =
      endpointSolenoidalEmbedding c
    exact endpointSpatialSolenoidal.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [map_sub, map_sub, hF, hc, sub_self]

/-- The projected integrated equation at a time recovers a periodic pressure
whose gradient is the Hölder residual after removing the solenoidal constant. -/
theorem exists_endpointPressure_of_projected_equation (F : HalfHolder A Vec3)
    (c : endpointHalfHolderSolenoidal)
    (hF : endpointWeakSpatialProjection (endpointHalfHolderToL2 F) =
      endpointSolenoidalEmbedding c) :
    ∃ p : Vec3 → ℝ, SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧
      ∀ x, HasGradientAt p
        (HalfHolder.eval (toUnitTorus x) (F - (c : HalfHolder A Vec3))) x := by
  let w : HalfHolder A Vec3 := F - (c : HalfHolder A Vec3)
  let g : C(A, Vec3) := ⟨w.val.1, w.val.1.continuous⟩
  have heq : g.toLp 2 unitTorusMeasure ℝ = endpointHalfHolderToL2 w := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure g,
      endpointHalfHolderToL2_apply_ae w] with a hg hw
    exact hg.trans hw.symm
  apply exists_endpointPressure_of_projection_eq_zero g
  rw [heq]
  exact endpointProjection_residual_eq_zero F c hF

/-- A time derivative of a curve of spatial projection-null fields stays in the
same nullspace, including with the one-sided derivatives at the endpoints. -/
theorem endpointProjection_eq_zero_of_derivWithin {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) {G : ℝ → C(A, Vec3)} {dG : C(A, Vec3)}
    (hD : HasDerivWithinAt G dG (Icc 0 T) t)
    (hG : ∀ r ∈ Icc 0 T, endpointWeakSpatialProjection ((G r).toLp 2 unitTorusMeasure ℝ) = 0) :
    endpointWeakSpatialProjection (dG.toLp 2 unitTorusMeasure ℝ) = 0 := by
  let Q := endpointWeakSpatialProjection.comp (ContinuousMap.toLp 2 unitTorusMeasure ℝ)
  have hq : HasDerivWithinAt (fun r => Q (G r)) (Q dG) (Icc 0 T) t :=
    Q.hasFDerivAt.comp_hasDerivWithinAt t hD
  have hz : HasDerivWithinAt (fun r => Q (G r)) 0 (Icc 0 T) t :=
    (hasDerivWithinAt_const t (Icc 0 T) (0 : endpointSpatialSolenoidal)).congr hG (hG t ht)
  exact (hq.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
    (hz.derivWithin (uniqueDiffOn_Icc hT t ht))

/-- The negative time derivative of the integrated pressure gradient is the
pressure gradient that appears in the momentum equation. -/
theorem hasDerivWithinAt_endpointIntegratedPressure {T t : ℝ}
    {G : ℝ → C(A, Vec3)} {dG : C(A, Vec3)} {q : Vec3 → ℝ}
    (hD : HasDerivWithinAt G dG (Icc 0 T) t)
    (hq : ∀ x, HasGradientAt q (-(dG (toUnitTorus x))) x) (x : Vec3) :
    HasDerivWithinAt (fun r => G r (toUnitTorus x)) (-(gradient q x)) (Icc 0 T) t := by
  have hEval := (ContinuousMap.evalCLM ℝ (toUnitTorus x)).hasFDerivAt.comp_hasDerivWithinAt t hD
  rw [(hq x).gradient, neg_neg]
  exact hEval

/-- The time-differentiated nullspace residual gives an actual periodic pressure
for use in the strong momentum equation. -/
theorem exists_endpointMomentumPressure_of_projection_eq_zero {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) {G : ℝ → C(A, Vec3)} {dG : C(A, Vec3)}
    (hD : HasDerivWithinAt G dG (Icc 0 T) t)
    (hG : ∀ r ∈ Icc 0 T, endpointWeakSpatialProjection ((G r).toLp 2 unitTorusMeasure ℝ) = 0) :
    ∃ q : Vec3 → ℝ, SpatiallyPeriodic q ∧ (∫ x in centeredCell, q x) = 0 ∧
      (∀ x, HasGradientAt q (-(dG (toUnitTorus x))) x) ∧
      ∀ x, HasDerivWithinAt (fun r => G r (toUnitTorus x)) (-(gradient q x)) (Icc 0 T) t := by
  have h : endpointWeakSpatialProjection ((-dG).toLp 2 unitTorusMeasure ℝ) = 0 := by
    simp only [map_neg, endpointProjection_eq_zero_of_derivWithin hT ht hD hG, neg_zero]
  obtain ⟨q, hper, hmean, hgrad⟩ := exists_endpointPressure_of_projection_eq_zero (-dG) h
  have hq (x : Vec3) : HasGradientAt q (-(dG (toUnitTorus x))) x := hgrad x
  exact ⟨q, hper, hmean, hq, fun x => hasDerivWithinAt_endpointIntegratedPressure hD hq x⟩

/-- Differentiate the integrated equation with an actual periodic pressure
reconstructed from the time derivative of the projected residual. -/
theorem exists_endpointStrongLabelMomentum_of_projected_residual {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (x : Vec3)
    {F M : ℝ → Vec3 →L[ℝ] Vec3} {v f : ℝ → Vec3} {dv c : Vec3}
    {G : ℝ → C(A, Vec3)} {dG : C(A, Vec3)}
    (hF : HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hv : HasDerivWithinAt v dv (Icc 0 T) t)
    (hD : HasDerivWithinAt G dG (Icc 0 T) t)
    (hG : ∀ r ∈ Icc 0 T, endpointWeakSpatialProjection ((G r).toLp 2 unitTorusMeasure ℝ) = 0)
    (hΩ : ContinuousOn (fun r => vorticityForm (F r) (M r) (v r)) (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T))
    (hEq : ∀ r ∈ Icc 0 T, kineticForm (F r) (v r) -
      (∫ s in (0 : ℝ)..r, vorticityForm (F s) (M s) (v s)) -
      (∫ s in (0 : ℝ)..r, f s) = c + G r (toUnitTorus x)) :
    ∃ q : Vec3 → ℝ, SpatiallyPeriodic q ∧ (∫ y in centeredCell, q y) = 0 ∧
      (∀ y, HasGradientAt q (-(dG (toUnitTorus y))) y) ∧
      kineticForm (F t) dv + gradient q x = f t -
        (2 : ℝ) • (F t).adjoint (M t (F t (v t))) := by
  obtain ⟨q, hper, hmean, hgrad, hq⟩ := exists_endpointMomentumPressure_of_projection_eq_zero hT ht hD hG
  exact ⟨q, hper, hmean, hgrad,
    strongLabelMomentum_of_integrated hT ht hF hv (hq x) hΩ hf hEq⟩

private theorem norm_le_one_of_mem_centeredCell_pressure {x : Vec3} (hx : x ∈ centeredCell) :
    ‖x‖ ≤ 1 := by
  have hcoord (i : Fin 3) : (x i) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hi : |x i| ≤ (1 / 2 : ℝ) := abs_le.mpr (hx i)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) hi 2
  have hs : ‖x‖ ^ 2 ≤ (3 / 4 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (1 / 2 : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := by norm_num
  nlinarith [norm_nonneg x]

private theorem centeredCell_volume_real_eq_one_pressure :
    (volume : Measure Vec3).real centeredCell = 1 := by
  let : IsProbabilityMeasure unitTorusMeasure :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)))
  have h := torusIntegral_eq_centeredCell (fun _ => (1 : ℝ))
  simpa only [integral_const, setIntegral_const, measureReal_def, Measure.restrict_apply_univ, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, mul_one] using h.symm

/-- On the unit torus, the mean-zero pressure has a supremum bound from its
spatial gradient, expressed on the whole periodic lift. -/
theorem norm_endpointMeanZeroPressure_le {p : Vec3 → ℝ} {g : Vec3 → Vec3} {M : ℝ}
    (hper : SpatiallyPeriodic p) (hmean : (∫ y in centeredCell, p y) = 0)
    (hgrad : ∀ y, HasGradientAt p (g y) y) (hM : ∀ y, ‖g y‖ ≤ M)
    (x : Vec3) : ‖p x‖ ≤ 2 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hp : Continuous p := continuous_iff_continuousAt.mpr fun y => (hgrad y).continuousAt
  have hIp : IntegrableOn p centeredCell := hp.continuousOn.integrableOn_compact isCompact_centeredCell
  have hdiff (u v : Vec3) : ‖p u - p v‖ ≤ M * ‖u - v‖ := by
    have hD (z : Vec3) (_ : z ∈ (univ : Set Vec3)) :
        HasFDerivWithinAt p (innerSL ℝ (g z)) univ z :=
      (hgrad z).hasFDerivAt.hasFDerivWithinAt
    have hN (z : Vec3) (_ : z ∈ (univ : Set Vec3)) : ‖innerSL ℝ (g z)‖ ≤ M := by
      change ‖InnerProductSpace.toDual ℝ Vec3 (g z)‖ ≤ M
      rw [(InnerProductSpace.toDual ℝ Vec3).norm_map]
      exact hM z
    exact (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hD hN (mem_univ v) (mem_univ u)
  obtain ⟨k, hk⟩ := exists_sub_latticeVector_mem_centeredCell x
  let z := x - latticeVector k
  have hz : z ∈ centeredCell := hk
  have hpx : p x = p z := by simpa only [z, sub_add_cancel] using hper k z
  have hInt : (∫ y in centeredCell, p z - p y) = p z := by
    have hIz : IntegrableOn (fun _ : Vec3 => p z) centeredCell :=
      integrableOn_const isCompact_centeredCell.measure_ne_top
    rw [integral_sub hIz hIp, hmean, sub_zero, setIntegral_const,
      centeredCell_volume_real_eq_one_pressure, one_smul]
  rw [hpx, ← hInt]
  calc
    _ ≤ (2 * M) * (volume : Measure Vec3).real centeredCell :=
      norm_setIntegral_le_of_norm_le_const isCompact_centeredCell.measure_lt_top fun y hy =>
        (hdiff z y).trans <| calc
          M * ‖z - y‖ ≤ M * (‖z‖ + ‖y‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) hM0
          _ ≤ M * (1 + 1) := mul_le_mul_of_nonneg_left
            (add_le_add (norm_le_one_of_mem_centeredCell_pressure hz)
              (norm_le_one_of_mem_centeredCell_pressure hy)) hM0
          _ = 2 * M := by ring
    _ = _ := by rw [centeredCell_volume_real_eq_one_pressure, mul_one]

end

end TorusEuler
