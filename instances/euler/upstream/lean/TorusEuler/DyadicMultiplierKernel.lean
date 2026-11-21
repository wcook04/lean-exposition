import TorusEuler.FourierConvolution
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Banach-valued Fourier kernels for the dyadic multiplier in Appendix A. -/

open MeasureTheory MeasureTheory.Measure Set
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap

namespace TorusEuler

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The weighted derivative integrals required for five integrations by parts
and at most one kernel derivative. -/
def multiplierDerivativeMass (symbol : Vec3 → F) : ℝ :=
  ∑ p ∈ Finset.range 2 ×ˢ Finset.range 6,
    ∫ ξ, ‖ξ‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 symbol ξ‖

theorem multiplierDerivativeMass_nonneg (symbol : Vec3 → F) :
    0 ≤ multiplierDerivativeMass symbol := by
  unfold multiplierDerivativeMass
  exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => by positivity

/-- On a fixed support ball the derivative integrals are controlled by the
uniform bound on the derivatives through order five. -/
theorem multiplierDerivativeMass_le_of_support {symbol : Vec3 → F} {R M : ℝ}
    (hSupport : tsupport symbol ⊆ Metric.closedBall 0 R)
    (hbound : ∀ n : ℕ, n ≤ 5 → ∀ ξ, ‖iteratedFDeriv ℝ n symbol ξ‖ ≤ M) :
    multiplierDerivativeMass symbol ≤ 12 * (max 1 R * M) * volume.real (Metric.closedBall (0 : Vec3) R) := by
  let ball : Set Vec3 := Metric.closedBall 0 R
  have hball : MeasurableSet ball := Metric.isClosed_closedBall.measurableSet
  have hfinite : volume ball < ⊤ := (isCompact_closedBall (0 : Vec3) R).measure_lt_top
  unfold multiplierDerivativeMass
  calc
    _ ≤ ∑ _ ∈ Finset.range 2 ×ˢ Finset.range 6, (max 1 R * M) * volume.real ball := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hm, hn⟩ := Finset.mem_product.mp hp
      let g (ξ : Vec3) := ‖ξ‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 symbol ξ‖
      have hg : ball.indicator g = g := by
        funext ξ
        by_cases hξ : ξ ∈ ball
        · exact Set.indicator_of_mem hξ _
        · have hzero : iteratedFDeriv ℝ p.2 symbol ξ = 0 :=
            Function.notMem_support.mp (fun h => hξ (hSupport (support_iteratedFDeriv_subset p.2 h)))
          simp [g, Set.indicator_of_notMem hξ, hzero]
      change (∫ ξ, g ξ) ≤ _
      rw [← hg, integral_indicator hball]
      have hpoint (ξ : Vec3) (hξ : ξ ∈ ball) : ‖g ξ‖ ≤ max 1 R * M := by
        have hξR : ‖ξ‖ ≤ R := by simpa only [ball, Metric.mem_closedBall, dist_zero_right] using hξ
        have hpow : ‖ξ‖ ^ p.1 ≤ max 1 R := by
          have hone : p.1 = 0 ∨ p.1 = 1 := by have := Finset.mem_range.mp hm; omega
          rcases hone with h | h
          · simp [h]
          · simpa [h] using hξR.trans (le_max_right (1 : ℝ) R)
        rw [Real.norm_of_nonneg (by unfold g; positivity)]
        exact mul_le_mul hpow (hbound _ (by have := Finset.mem_range.mp hn; omega) ξ)
          (norm_nonneg _) ((show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _))
      exact le_abs_self _ |>.trans (norm_setIntegral_le_of_norm_le_const_ae' hfinite
        (Filter.Eventually.of_forall hpoint))
    _ = _ := by
      simp [Finset.card_product, ball]
      ring

private theorem multiplierDerivativeMass_sum_bound (symbol : Vec3 → F)
    {d n : ℕ} (hd : d ≤ 1) (hn : n ≤ 5) :
    (∑ p ∈ Finset.range (d + 1) ×ˢ Finset.range (n + 1),
      ∫ ξ, ‖ξ‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 symbol ξ‖) ≤ multiplierDerivativeMass symbol := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.product_subset_product (Finset.range_mono (by omega))
      (Finset.range_mono (by omega))
  · exact fun _ _ _ => integral_nonneg fun _ => by positivity

private theorem inverseMultiplierKernel_pow_mul_le [CompleteSpace F] (symbol : 𝓢(Vec3, F))
    {d n : ℕ} (hd : d ≤ 1) (hn : n ≤ 5) (y : Vec3) :
    ‖y‖ ^ n * ‖iteratedFDeriv ℝ d (𝓕⁻ symbol : 𝓢(Vec3, F)) y‖ ≤
      (1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * multiplierDerivativeMass symbol := by
  have hFourier := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (f := (symbol : Vec3 → F)) (K := ⊤) (k := d) (n := n)
    (symbol.smooth ⊤) (fun k n _ _ => symbol.integrable_pow_mul_iteratedFDeriv volume k n)
    le_top le_top (-y)
  have hneg :
      ‖iteratedFDeriv ℝ d (𝓕⁻ symbol : 𝓢(Vec3, F)) y‖ =
        ‖iteratedFDeriv ℝ d (𝓕 (symbol : Vec3 → F)) (-y)‖ := by
    rw [SchwartzMap.fourierInv_coe]
    simp_rw [show (𝓕⁻ (symbol : Vec3 → F)) =
      (𝓕 (symbol : Vec3 → F)) ∘ LinearIsometryEquiv.neg ℝ (E := Vec3) by
        funext x
        exact Real.fourierInv_eq_fourier_neg symbol x]
    exact (LinearIsometryEquiv.neg ℝ (E := Vec3)).norm_iteratedFDeriv_comp_right _ y d
  rw [hneg, ← norm_neg y]
  refine hFourier.trans ?_
  have hπ : (2 * Real.pi) ^ d ≤ 1 + 2 * Real.pi := by
    interval_cases d <;> simp [Real.pi_nonneg]
  have h4 : (2 * (d : ℝ) + 2) ^ n ≤ (4 : ℝ) ^ 5 := by
    have hd' : (d : ℝ) ≤ 1 := by exact_mod_cast hd
    exact (pow_le_pow_left₀ (by positivity) (show 2 * (d : ℝ) + 2 ≤ 4 by linarith) _).trans
      (pow_le_pow_right₀ (by norm_num) hn)
  gcongr
  exact multiplierDerivativeMass_sum_bound symbol hd hn

/-- Inverse Fourier integration gives order-five decay for the kernel and its
first derivative, in the norm of an arbitrary complex Banach space. -/
theorem inverseMultiplierKernel_decay [CompleteSpace F] (symbol : 𝓢(Vec3, F))
    {d : ℕ} (hd : d ≤ 1) (y : Vec3) :
    (1 + ‖y‖) ^ 5 * ‖iteratedFDeriv ℝ d (𝓕⁻ symbol : 𝓢(Vec3, F)) y‖ ≤
      32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * multiplierDerivativeMass symbol) := by
  rcases le_total ‖y‖ 1 with hy | hy
  · have hw : (1 + ‖y‖) ^ 5 ≤ 32 := by
      have := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖y‖)
        (show 1 + ‖y‖ ≤ 2 by linarith) 5
      norm_num at this ⊢
      exact this
    refine (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [pow_zero, one_mul] using inverseMultiplierKernel_pow_mul_le symbol hd
      (n := 0) (by omega) y
  · have hw : (1 + ‖y‖) ^ 5 ≤ 32 * ‖y‖ ^ 5 := by
      have := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖y‖)
        (show 1 + ‖y‖ ≤ 2 * ‖y‖ by linarith) 5
      simpa only [mul_pow, show (2 : ℝ) ^ 5 = 32 by norm_num] using this
    refine (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (inverseMultiplierKernel_pow_mul_le symbol hd le_rfl y)
      (by norm_num)

/-- The Euclidean kernel at scale `Λ`, before applying it to a periodic lift. -/
def scaledMultiplierKernel (Λ : ℝ) (K : Vec3 → F) (y : Vec3) : F :=
  Λ ^ 3 • K (Λ • y)

theorem scaledMultiplierKernel_decay [CompleteSpace F] (symbol : 𝓢(Vec3, F))
    {Λ : ℝ} (hΛ : 0 < Λ) {d : ℕ} (hd : d ≤ 1) (y : Vec3) :
    (1 + Λ * ‖y‖) ^ 5 *
        ‖iteratedFDeriv ℝ d (scaledMultiplierKernel Λ (𝓕⁻ symbol : 𝓢(Vec3, F))) y‖ ≤
      Λ ^ (3 + d) * (32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * multiplierDerivativeMass symbol)) := by
  let K : 𝓢(Vec3, F) := 𝓕⁻ symbol
  have hcomp : ContDiff ℝ d (fun z : Vec3 => K (Λ • z)) :=
    (K.smooth d).comp (contDiff_id.const_smul Λ)
  change (1 + Λ * ‖y‖) ^ 5 *
    ‖iteratedFDeriv ℝ d (fun z : Vec3 => Λ ^ 3 • K (Λ • z)) y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hcomp.contDiffAt,
    iteratedFDeriv_comp_const_smul Λ (K.smooth d), norm_smul, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hΛ.le _), Real.norm_of_nonneg (pow_nonneg hΛ.le _)]
  have hnorm : ‖Λ • y‖ = Λ * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hΛ.le]
  rw [← hnorm]
  calc
    _ = Λ ^ (3 + d) * ((1 + ‖Λ • y‖) ^ 5 * ‖iteratedFDeriv ℝ d K (Λ • y)‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inverseMultiplierKernel_decay symbol hd (Λ • y))
      (pow_nonneg hΛ.le _)

/-- The inverse transform of a smooth compactly supported Banach-valued symbol. -/
def compactMultiplierKernel [CompleteSpace F] {symbol : Vec3 → F}
    (hSupport : HasCompactSupport symbol) (hs : ContDiff ℝ ∞ symbol) : 𝓢(Vec3, F) :=
  𝓕⁻ (hSupport.toSchwartzMap hs)

theorem fourier_compactMultiplierKernel [CompleteSpace F] {symbol : Vec3 → F}
    (hSupport : HasCompactSupport symbol) (hs : ContDiff ℝ ∞ symbol) (ξ : Vec3) :
    (𝓕 (compactMultiplierKernel hSupport hs : Vec3 → F)) ξ = symbol ξ := by
  rw [← SchwartzMap.fourier_coe, compactMultiplierKernel, FourierTransform.fourier_fourierInv_eq]
  rfl

private theorem integral_mul_scale {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Λ : ℝ} (hΛ : 0 < Λ) (g : Vec3 → G) :
    (∫ y : Vec3, Λ ^ 3 • g (Λ • y)) = ∫ y, g y := by
  rw [integral_smul, integral_comp_smul_of_nonneg volume g Λ (hR := hΛ.le),
    finrank_euclideanSpace_fin, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hΛ.ne'), one_smul]

theorem integrable_scaledMultiplierKernel {Λ : ℝ} (hΛ : 0 < Λ) {K : Vec3 → F}
    (hK : Integrable K) : Integrable (scaledMultiplierKernel Λ K) := by
  change Integrable ((Λ ^ 3 : ℝ) • (fun y : Vec3 => K (Λ • y)))
  exact ((integrable_comp_smul_iff volume K hΛ.ne').mpr hK).smul (Λ ^ 3 : ℝ)

theorem integral_norm_scaledMultiplierKernel {Λ : ℝ} (hΛ : 0 < Λ) (K : Vec3 → F) :
    (∫ y, ‖scaledMultiplierKernel Λ K y‖) = ∫ y, ‖K y‖ := by
  simpa only [scaledMultiplierKernel, norm_smul, Real.norm_of_nonneg (pow_nonneg hΛ.le _),
    smul_eq_mul] using integral_mul_scale hΛ (fun y => ‖K y‖)

theorem fourier_scaledMultiplierKernel {Λ : ℝ} (hΛ : 0 < Λ) (K : Vec3 → F) (ξ : Vec3) :
    (𝓕 (scaledMultiplierKernel Λ K)) ξ = (𝓕 K) (Λ⁻¹ • ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  let g (y : Vec3) :=
    Complex.exp ((↑(-2 * Real.pi * ⟪y, Λ⁻¹ • ξ⟫) : ℂ) * Complex.I) • K y
  rw [← integral_mul_scale hΛ g]
  congr 1
  funext y
  have hinner : ⟪Λ • y, Λ⁻¹ • ξ⟫ = ⟪y, ξ⟫ := by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul]
  dsimp only [g]
  rw [hinner, scaledMultiplierKernel, smul_comm]

/-- A localized symbol vanishing at zero yields a kernel with zero integral. -/
theorem integral_scaledCompactMultiplierKernel [CompleteSpace F] {symbol : Vec3 → F}
    (hSupport : HasCompactSupport symbol) (hs : ContDiff ℝ ∞ symbol)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ y, scaledMultiplierKernel Λ (compactMultiplierKernel hSupport hs) y) = symbol 0 := by
  let K : Vec3 → F := compactMultiplierKernel hSupport hs
  have h : (𝓕 K) 0 = symbol 0 := fourier_compactMultiplierKernel hSupport hs 0
  rw [Real.fourier_eq'] at h
  exact (integral_mul_scale hΛ K).trans
    (by simpa only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul] using h)

theorem integral_sqrtNorm_scaledMultiplierKernel {Λ : ℝ} (hΛ : 0 < Λ) (K : Vec3 → F) :
    (∫ y, ‖scaledMultiplierKernel Λ K y‖ * Real.sqrt ‖y‖) =
      Real.sqrt Λ⁻¹ * ∫ y, ‖K y‖ * Real.sqrt ‖y‖ := by
  let g (y : Vec3) := ‖K y‖ * Real.sqrt ‖y‖
  change _ = Real.sqrt Λ⁻¹ * ∫ y, g y
  rw [← integral_mul_scale hΛ g, ← integral_const_mul]
  congr 1
  funext y
  have hroot : Real.sqrt Λ⁻¹ * Real.sqrt ‖Λ • y‖ = Real.sqrt ‖y‖ := by
    rw [norm_smul, Real.norm_of_nonneg hΛ.le, ← Real.sqrt_mul (inv_nonneg.mpr hΛ.le),
      ← mul_assoc, inv_mul_cancel₀ hΛ.ne', one_mul]
  change ‖Λ ^ 3 • K (Λ • y)‖ * Real.sqrt ‖y‖ =
    Real.sqrt Λ⁻¹ * (Λ ^ 3 * (‖K (Λ • y)‖ * Real.sqrt ‖Λ • y‖))
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hΛ.le _), ← hroot]
  ring

private theorem integrable_sqrtNorm_mul_norm_schwartz (K : 𝓢(Vec3, F)) :
    Integrable (fun y => ‖K y‖ * Real.sqrt ‖y‖) := by
  have hmajor : Integrable (fun y => ‖K y‖ + ‖y‖ * ‖K y‖) := by
    exact K.integrable.norm.add (by simpa only [pow_one] using K.integrable_pow_mul volume 1)
  have hcont : Continuous (fun y => ‖K y‖ * Real.sqrt ‖y‖) :=
    K.continuous.norm.mul (Real.continuous_sqrt.comp continuous_norm)
  apply hmajor.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
    have hs : Real.sqrt ‖y‖ ≤ 1 + ‖y‖ := by
      have h := Real.sq_sqrt (norm_nonneg y)
      nlinarith [sq_nonneg (Real.sqrt ‖y‖ - 1)]
    calc
      _ ≤ ‖K y‖ * (1 + ‖y‖) := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ = _ := by ring)

theorem integrable_sqrtNorm_mul_norm_scaledMultiplierKernel {Λ : ℝ} (hΛ : 0 < Λ)
    (K : 𝓢(Vec3, F)) :
    Integrable (fun y => ‖scaledMultiplierKernel Λ K y‖ * Real.sqrt ‖y‖) := by
  let G : 𝓢(Vec3, F) := Λ ^ 3 • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 Λ hΛ.ne')) K
  exact integrable_sqrtNorm_mul_norm_schwartz G

section OperatorConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Convolution with an operator-valued Euclidean kernel on the periodic lift. -/
def operatorLiftConvolution (K : Vec3 → E →L[ℂ] F) (f : Vec3 → E) (x : Vec3) : F :=
  ∫ y, K y (f (x - y))

theorem spatiallyPeriodic_operatorLiftConvolution (K : Vec3 → E →L[ℂ] F) {f : Vec3 → E}
    (hf : SpatiallyPeriodic f) : SpatiallyPeriodic (operatorLiftConvolution K f) := by
  intro n x
  unfold operatorLiftConvolution
  congr 1
  funext y
  rw [show x + latticeVector n - y = x - y + latticeVector n by abel, hf]

theorem integrable_operatorLiftConvolution {K : Vec3 → E →L[ℂ] F} (hK : Integrable K)
    {f : Vec3 → E} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Vec3) :
    Integrable (fun y => K y (f (x - y))) := by
  apply (hK.norm.mul_const M).mono'
    ((ContinuousLinearMap.apply ℂ F).aestronglyMeasurable_comp₂
      (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable hK.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => (K y).le_opNorm_of_le (hM _)

theorem norm_operatorLiftConvolution_le {K : Vec3 → E →L[ℂ] F} (hK : Integrable K)
    {f : Vec3 → E} {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Vec3) :
    ‖operatorLiftConvolution K f x‖ ≤ (∫ y, ‖K y‖) * M := by
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => norm_nonneg (K y (f (x - y))))
    (hK.norm.mul_const M) (Filter.Eventually.of_forall fun y => (K y).le_opNorm_of_le (hM _))
  rw [integral_mul_const] at h
  exact (norm_integral_le_integral_norm _).trans h

/-- Subtract the input value at the center against a kernel of zero mean. -/
theorem norm_operatorLiftConvolution_le_halfHolder [CompleteSpace F]
    {K : Vec3 → E →L[ℂ] F} (hK : Integrable K)
    (hMoment : Integrable (fun y => ‖K y‖ * Real.sqrt ‖y‖))
    (hzero : (∫ y, K y) = 0) {f : Vec3 → E} (hf : Continuous f)
    {M H : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hH : ∀ x y, ‖f x - f y‖ ≤ H * Real.sqrt ‖x - y‖)
    (x : Vec3) :
    ‖operatorLiftConvolution K f x‖ ≤ H * ∫ y, ‖K y‖ * Real.sqrt ‖y‖ := by
  let g (y : Vec3) := K y (f (x - y) - f x)
  have hCenter : Integrable (fun y => K y (f x)) :=
    (ContinuousLinearMap.apply ℂ F (f x)).integrable_comp hK
  have hsubtract : operatorLiftConvolution K f x = ∫ y, g y := by
    simp only [g, map_sub]
    rw [integral_sub (integrable_operatorLiftConvolution hK hf hM x) hCenter,
      ← ContinuousLinearMap.integral_apply hK (f x), hzero]
    simp [operatorLiftConvolution]
  rw [hsubtract]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hMoment.const_mul H)
  exact Filter.Eventually.of_forall (fun y => by
    have hy : ‖x - y - x‖ = ‖y‖ := by rw [show x - y - x = -y by abel, norm_neg]
    have h := (hH (x - y) x)
    rw [hy] at h
    calc
      ‖g y‖ ≤ ‖K y‖ * (H * Real.sqrt ‖y‖) := (K y).le_opNorm_of_le h
      _ = H * (‖K y‖ * Real.sqrt ‖y‖) := by ring)

/-- A canceled dyadic block gains one half-power of the scale in the supremum norm. -/
theorem norm_operatorLiftConvolution_dyadic_le_halfHolder [CompleteSpace F]
    {symbol : Vec3 → E →L[ℂ] F} (hSupport : HasCompactSupport symbol)
    (hs : ContDiff ℝ ∞ symbol) (hzero : symbol 0 = 0) {Λ : ℝ} (hΛ : 0 < Λ)
    {f : Vec3 → E} (hf : Continuous f) {M H : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (hH : ∀ x y, ‖f x - f y‖ ≤ H * Real.sqrt ‖x - y‖) (x : Vec3) :
    let K : 𝓢(Vec3, E →L[ℂ] F) := compactMultiplierKernel hSupport hs
    ‖operatorLiftConvolution (scaledMultiplierKernel Λ K) f x‖ ≤
      H * (Real.sqrt Λ⁻¹ * ∫ y, ‖K y‖ * Real.sqrt ‖y‖) := by
  dsimp only
  rw [← integral_sqrtNorm_scaledMultiplierKernel hΛ]
  exact norm_operatorLiftConvolution_le_halfHolder
    (integrable_scaledMultiplierKernel hΛ (compactMultiplierKernel hSupport hs).integrable)
    (integrable_sqrtNorm_mul_norm_scaledMultiplierKernel hΛ _)
    ((integral_scaledCompactMultiplierKernel hSupport hs hΛ).trans hzero) hf hM hH x

private theorem fourierMode_sub_eq_exp_mul (k : Fin 3 → ℤ) (x y : Vec3) :
    fourierMode k (x - y) =
      Complex.exp ((↑(-2 * Real.pi * ⟪y, latticeVector k⟫) : ℂ) * Complex.I) * fourierMode k x := by
  rw [fourierMode_eq_exp, fourierMode_eq_exp k x, ← Complex.exp_add]
  congr 1
  simp only [PiLp.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, latticeVector,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_sum,
    Complex.ofReal_intCast]
  ring

theorem operatorLiftConvolution_fourierMode_smul [CompleteSpace F]
    {K : Vec3 → E →L[ℂ] F} (hK : Integrable K)
    (k : Fin 3 → ℤ) (a : E) (x : Vec3) :
    operatorLiftConvolution K (fun z => fourierMode k z • a) x =
      fourierMode k x • (((𝓕 K) (latticeVector k)) a) := by
  rw [operatorLiftConvolution, Real.fourier_eq', ContinuousLinearMap.integral_apply]
  · rw [← integral_smul]
    congr 1
    funext y
    rw [fourierMode_sub_eq_exp_mul, map_smul, ← smul_smul, _root_.smul_apply, smul_comm]
  · let phase (y : Vec3) := Complex.exp ((↑(-2 * Real.pi * ⟪y, latticeVector k⟫) : ℂ) * Complex.I)
    have hphase : Continuous phase := Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul
        (continuous_id.inner continuous_const))).mul continuous_const)
    change Integrable (phase • K)
    exact hK.bdd_smul 1 hphase.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I
        (-2 * Real.pi * ⟪y, latticeVector k⟫)).le)

/-- The multiplier on torus trigonometric polynomials is convolution on the lift
by the dilated inverse transform of its smooth localized symbol. -/
theorem operatorLiftConvolution_compactMultiplierKernel_finiteFourierSum [CompleteSpace F]
    {symbol : Vec3 → E →L[ℂ] F} (hSupport : HasCompactSupport symbol) (hs : ContDiff ℝ ∞ symbol)
    {Λ : ℝ} (hΛ : 0 < Λ) (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) (x : Vec3) :
    operatorLiftConvolution (scaledMultiplierKernel Λ (compactMultiplierKernel hSupport hs))
        (fun z => finiteFourierSum s a (toUnitTorus z)) x =
      finiteFourierSum s (fun k => symbol (Λ⁻¹ • latticeVector k) (a k)) (toUnitTorus x) := by
  let K := scaledMultiplierKernel Λ (compactMultiplierKernel hSupport hs)
  have hK : Integrable K := integrable_scaledMultiplierKernel hΛ
    (compactMultiplierKernel hSupport hs).integrable
  change (∫ y, K y (∑ k ∈ s, fourierMode k (x - y) • a k)) = _
  simp only [_root_.map_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    simpa only [K, fourier_scaledMultiplierKernel hΛ, fourier_compactMultiplierKernel,
      operatorLiftConvolution, fourierMode] using
      operatorLiftConvolution_fourierMode_smul hK k (a k) x
  · intro k _
    refine integrable_operatorLiftConvolution hK
      ((contDiff_fourierMode k).continuous.smul continuous_const) (M := ‖a k‖) (fun y => ?_) x
    change ‖fourierMode k y • a k‖ ≤ ‖a k‖
    rw [norm_smul, norm_fourierMode, one_mul]

end OperatorConvolution

end

end TorusEuler
