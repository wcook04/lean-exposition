import TorusEuler.TorusFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The Euclidean convolution formula for the frequency cutoff of Appendix B. -/

open MeasureTheory MeasureTheory.Measure Set
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap

namespace TorusEuler

noncomputable section

section Convolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]

/-- Convolution of a field on the Euclidean lift against a scalar integrable kernel. -/
def liftConvolution (K : Vec3 → 𝕜) (f : Vec3 → E) (x : Vec3) : E :=
  ∫ y, K y • f (x - y)

theorem spatiallyPeriodic_liftConvolution (K : Vec3 → 𝕜) {f : Vec3 → E}
    (hf : SpatiallyPeriodic f) : SpatiallyPeriodic (liftConvolution K f) := by
  intro n x
  unfold liftConvolution
  congr 1
  funext y
  rw [show x + latticeVector n - y = x - y + latticeVector n by abel, hf]

omit [NormedSpace ℝ E] in
theorem integrable_liftConvolution {K : Vec3 → 𝕜} (hK : Integrable K)
    {f : Vec3 → E} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Vec3) :
    Integrable (fun y => K y • f (x - y)) := by
  apply (hK.norm.mul_const M).mono'
    (hK.aestronglyMeasurable.smul (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    change ‖K y • f (x - y)‖ ≤ ‖K y‖ * M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM (x - y)) (norm_nonneg _)

theorem norm_liftConvolution_le {K : Vec3 → 𝕜} (hK : Integrable K)
    {f : Vec3 → E} {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Vec3) :
    ‖liftConvolution K f x‖ ≤ (∫ y, ‖K y‖) * M := by
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => norm_nonneg (K y • f (x - y)))
    (hK.norm.mul_const M) (Filter.Eventually.of_forall fun y => by
      change ‖K y • f (x - y)‖ ≤ ‖K y‖ * M
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM (x - y)) (norm_nonneg _))
  rw [integral_mul_const] at h
  exact (norm_integral_le_integral_norm _).trans h

theorem norm_liftConvolution_increment_le {K : Vec3 → 𝕜} (hK : Integrable K)
    [CompleteSpace E] {f : Vec3 → E} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (x v : Vec3) {D : ℝ} (hD : ∀ z, ‖f (z + v) - f z‖ ≤ D) :
    ‖liftConvolution K f (x + v) - liftConvolution K f x‖ ≤ (∫ y, ‖K y‖) * D := by
  have h := norm_liftConvolution_le hK hD x
  unfold liftConvolution at *
  rw [← integral_sub (integrable_liftConvolution hK hf hM _)
    (integrable_liftConvolution hK hf hM _)]
  simpa only [smul_sub, show ∀ y : Vec3, x + v - y = x - y + v by intro y; abel] using h

end Convolution

private theorem fourierMode_sub (k : Fin 3 → ℤ) (x y : Vec3) :
    fourierMode k (x - y) = fourierMode k x * fourierMode k (-y) := by
  rw [fourierMode_eq_exp, fourierMode_eq_exp k x, fourierMode_eq_exp k (-y), ← Complex.exp_add]
  congr 1
  simp only [PiLp.sub_apply, PiLp.neg_apply, Complex.ofReal_sub, Complex.ofReal_neg,
    mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

private theorem fourierMode_neg_eq_fourierFactor (k : Fin 3 → ℤ) (y : Vec3) :
    fourierMode k (-y) = Complex.exp ((↑(-2 * Real.pi * ⟪y, latticeVector k⟫) : ℂ) * Complex.I) := by
  rw [fourierMode_eq_exp]
  congr 1
  simp only [PiLp.neg_apply, Complex.ofReal_neg, mul_neg, Finset.sum_neg_distrib,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    latticeVector, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_sum]
  simp only [Complex.ofReal_intCast]
  ring

/-- A Fourier character lifted from the torus is an eigenfunction of Euclidean convolution. -/
theorem liftConvolution_fourierMode_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (K : Vec3 → ℂ) (k : Fin 3 → ℤ) (a : E) (x : Vec3) :
    liftConvolution K (fun z => fourierMode k z • a) x =
      fourierMode k x • ((𝓕 K) (latticeVector k) • a) := by
  rw [Real.fourier_eq', liftConvolution]
  simp only [← fourierMode_neg_eq_fourierFactor, smul_eq_mul]
  rw [← integral_smul_const, ← integral_smul]
  congr 1
  funext y
  rw [fourierMode_sub, smul_smul, smul_smul]
  congr 1
  ring

theorem liftConvolution_fourierMode (K : Vec3 → ℂ) (k : Fin 3 → ℤ) (x : Vec3) :
    liftConvolution K (fourierMode k) x = (𝓕 K) (latticeVector k) * fourierMode k x := by
  rw [mul_comm]
  simpa only [smul_eq_mul, mul_one] using liftConvolution_fourierMode_smul K k (1 : ℂ) x

/-- The Euclidean dilation of the Appendix B kernel, including its Jacobian. -/
def scaledLiftKernel (Λ : ℝ) (K : Vec3 → ℂ) (y : Vec3) : ℂ :=
  Λ ^ 3 • K (Λ • y)

theorem integrable_scaledLiftKernel {Λ : ℝ} (hΛ : 0 < Λ) {K : Vec3 → ℂ} (hK : Integrable K) :
    Integrable (scaledLiftKernel Λ K) := by
  change Integrable ((Λ ^ 3 : ℝ) • (fun y : Vec3 => K (Λ • y)))
  exact ((integrable_comp_smul_iff volume K hΛ.ne').mpr hK).smul (Λ ^ 3 : ℝ)

private theorem integral_scaled {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Λ : ℝ} (hΛ : 0 < Λ) (g : Vec3 → F) :
    (∫ y : Vec3, Λ ^ 3 • g (Λ • y)) = ∫ y, g y := by
  rw [integral_smul, integral_comp_smul_of_nonneg volume g Λ (hR := hΛ.le),
    finrank_euclideanSpace_fin, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hΛ.ne'), one_smul]

theorem integral_norm_scaledLiftKernel {Λ : ℝ} (hΛ : 0 < Λ) (K : Vec3 → ℂ) :
    (∫ y, ‖scaledLiftKernel Λ K y‖) = ∫ y, ‖K y‖ := by
  simpa only [scaledLiftKernel, norm_smul, Real.norm_of_nonneg (pow_nonneg hΛ.le _),
    smul_eq_mul] using integral_scaled hΛ (fun y => ‖K y‖)

/-- Dilation rescales each absolute kernel moment by the inverse power of the scale. -/
theorem integral_norm_pow_scaledLiftKernel {Λ : ℝ} (hΛ : 0 < Λ) (K : Vec3 → ℂ) (j : ℕ) :
    (∫ y, ‖y‖ ^ j * ‖scaledLiftKernel Λ K y‖) =
      (Λ⁻¹) ^ j * ∫ y, ‖y‖ ^ j * ‖K y‖ := by
  let g (y : Vec3) := ‖y‖ ^ j * ‖K y‖
  change (∫ y, ‖y‖ ^ j * ‖scaledLiftKernel Λ K y‖) = (Λ⁻¹) ^ j * ∫ y, g y
  rw [← integral_scaled hΛ g, ← integral_const_mul]
  congr 1
  funext y
  simp only [scaledLiftKernel, norm_smul, Real.norm_of_nonneg hΛ.le,
    Real.norm_of_nonneg (pow_nonneg hΛ.le _), g, smul_eq_mul, mul_pow, inv_pow]
  field_simp

theorem fourier_scaledLiftKernel {Λ : ℝ} (hΛ : 0 < Λ) (K : Vec3 → ℂ) (ξ : Vec3) :
    (𝓕 (scaledLiftKernel Λ K)) ξ = (𝓕 K) (Λ⁻¹ • ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  let g (y : Vec3) :=
    Complex.exp ((↑(-2 * Real.pi * ⟪y, Λ⁻¹ • ξ⟫) : ℂ) * Complex.I) • K y
  rw [← integral_scaled hΛ g]
  congr 1
  funext y
  have hinner : ⟪Λ • y, Λ⁻¹ • ξ⟫ = ⟪y, ξ⟫ := by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul]
  dsimp only [g]
  rw [hinner, scaledLiftKernel, smul_comm]

private theorem hasCompactSupport_complexSymbol {ψ : Vec3 → ℝ}
    (hψ : ∀ x, 2 < ‖x‖ → ψ x = 0) : HasCompactSupport (fun x => (ψ x : ℂ)) := by
  apply (isCompact_closedBall (0 : Vec3) 2).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  change (ψ x : ℂ) ≠ 0 at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_not_gt (fun h => hx (by rw [hψ x h, Complex.ofReal_zero]))

/-- The Schwartz kernel obtained by inverting a smooth compactly supported
real symbol on the Euclidean lift. -/
def cutoffSchwartzKernel {ψ : Vec3 → ℝ} (hψ : ∀ x, 2 < ‖x‖ → ψ x = 0)
    (hs : ContDiff ℝ ∞ ψ) : 𝓢(Vec3, ℂ) :=
  𝓕⁻ ((hasCompactSupport_complexSymbol hψ).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs))

theorem fourier_cutoffSchwartzKernel {ψ : Vec3 → ℝ} (hψ : ∀ x, 2 < ‖x‖ → ψ x = 0)
    (hs : ContDiff ℝ ∞ ψ) (ξ : Vec3) :
    (𝓕 (cutoffSchwartzKernel hψ hs : Vec3 → ℂ)) ξ = (ψ ξ : ℂ) := by
  rw [← SchwartzMap.fourier_coe, cutoffSchwartzKernel, FourierTransform.fourier_fourierInv_eq]
  rfl

theorem integral_scaledCutoffSchwartzKernel {ψ : Vec3 → ℝ}
    (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ) {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ y, scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y) = (ψ 0 : ℂ) := by
  have h := fourier_cutoffSchwartzKernel hψ hs 0
  rw [Real.fourier_eq'] at h
  exact (integral_scaled hΛ (cutoffSchwartzKernel hψ hs : Vec3 → ℂ)).trans
    (by simpa only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul] using h)

section FourierSynthesis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem liftConvolution_lift_finiteFourierSum {K : Vec3 → ℂ} (hK : Integrable K)
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) (x : Vec3) :
    liftConvolution K (fun z => finiteFourierSum s a (toUnitTorus z)) x =
      finiteFourierSum s (fun k => (𝓕 K) (latticeVector k) • a k) (toUnitTorus x) := by
  change (∫ y, K y • ∑ k ∈ s, fourierMode k (x - y) • a k) = _
  simp only [Finset.smul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => liftConvolution_fourierMode_smul K k (a k) x
  · intro k _
    refine integrable_liftConvolution hK ((contDiff_fourierMode k).continuous.smul continuous_const)
      (M := ‖a k‖) (fun y => ?_) x
    change ‖fourierMode k y • a k‖ ≤ ‖a k‖
    simp only [norm_smul, norm_fourierMode, one_mul, le_refl]

private theorem smoothFourierCutoff_finiteFourierSum {ψ : Vec3 → ℝ} {Λ : ℝ} (hΛ : 0 < Λ)
    (hψ : ∀ x, 2 < ‖x‖ → ψ x = 0) (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → E) (z : UnitAddTorus (Fin 3)) :
    smoothFourierCutoff ψ Λ (finiteFourierSum s a) z =
      finiteFourierSum s (fun k => ψ (Λ⁻¹ • latticeVector k) • a k) z := by
  classical
  let b (k : Fin 3 → ℤ) := UnitAddTorus.mFourier k z • (ψ (Λ⁻¹ • latticeVector k) • a k)
  simp only [smoothFourierCutoff, finiteFourierSum, mFourierCoeff_finiteFourierSum, smul_ite, smul_zero]
  change (∑ k ∈ frequencyBand (2 * Λ), if k ∈ s then b k else 0) = ∑ k ∈ s, b k
  rw [← Finset.sum_filter]
  apply Finset.sum_subset (fun k hk => (Finset.mem_filter.mp hk).2)
  intro k hk hout
  have hband : k ∉ frequencyBand (2 * Λ) :=
    fun hm => hout (Finset.mem_filter.mpr ⟨hm, hk⟩)
  have hscaled : 2 < ‖Λ⁻¹ • latticeVector k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ), ← div_eq_inv_mul,
      lt_div_iff₀ hΛ]
    simpa using hband
  simp only [b, hψ _ hscaled, zero_smul, smul_zero]

/-- Convolution with the dilated Euclidean kernel agrees with the torus cutoff on
trigonometric polynomials when its Fourier transform is the prescribed symbol. -/
theorem liftConvolution_scaledLiftKernel_finiteFourierSum {K : Vec3 → ℂ} (hK : Integrable K)
    {ψ : Vec3 → ℝ} (htransform : ∀ ξ, (𝓕 K) ξ = (ψ ξ : ℂ))
    (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) {Λ : ℝ} (hΛ : 0 < Λ)
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) (x : Vec3) :
    liftConvolution (scaledLiftKernel Λ K) (fun z => finiteFourierSum s a (toUnitTorus z)) x =
      smoothFourierCutoff ψ Λ (finiteFourierSum s a) (toUnitTorus x) := by
  rw [liftConvolution_lift_finiteFourierSum (integrable_scaledLiftKernel hΛ hK),
    smoothFourierCutoff_finiteFourierSum hΛ hψ]
  simp only [fourier_scaledLiftKernel hΛ, htransform, Complex.coe_smul]

/-- The Schwartz inverse transform of the Appendix B symbol realizes the torus
cutoff on every trigonometric polynomial. -/
theorem liftConvolution_cutoffSchwartzKernel_finiteFourierSum {ψ : Vec3 → ℝ}
    (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ) {Λ : ℝ} (hΛ : 0 < Λ)
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) (x : Vec3) :
    liftConvolution (scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs))
      (fun z => finiteFourierSum s a (toUnitTorus z)) x =
      smoothFourierCutoff ψ Λ (finiteFourierSum s a) (toUnitTorus x) :=
  liftConvolution_scaledLiftKernel_finiteFourierSum (cutoffSchwartzKernel hψ hs).integrable
    (fourier_cutoffSchwartzKernel hψ hs) hψ hΛ s a x

end FourierSynthesis

end

end TorusEuler
