import TorusEuler.FourierConvolution
import Mathlib.Analysis.Calculus.Taylor

/-! Moment cancellation and Taylor remainders for the kernel of Appendix B. -/

open Filter MeasureTheory
open scoped ContDiff FourierTransform Nat RealInnerProductSpace SchwartzMap Topology

namespace TorusEuler

noncomputable section

/-- Dilation with the Jacobian preserves the Schwartz class. -/
def scaledSchwartzKernel (Λ : ℝ) (hΛ : Λ ≠ 0) (K : 𝓢(Vec3, ℂ)) : 𝓢(Vec3, ℂ) :=
  Λ ^ 3 • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 Λ hΛ)) K

theorem scaledSchwartzKernel_apply (Λ : ℝ) (hΛ : Λ ≠ 0) (K : 𝓢(Vec3, ℂ)) (y : Vec3) :
    scaledSchwartzKernel Λ hΛ K y = scaledLiftKernel Λ K y :=
  rfl

/-- Every positive-degree moment in a list of directions is determined by the
corresponding iterated Fourier derivative at zero. -/
theorem iteratedFDeriv_fourier_schwartz_zero (K : 𝓢(Vec3, ℂ)) (j : ℕ) (v : Fin j → Vec3) :
    iteratedFDeriv ℝ j (𝓕 (K : Vec3 → ℂ)) 0 v =
      (-(2 * (Real.pi : ℂ) * Complex.I)) ^ j •
        ∫ y, (∏ i, ⟪y, v i⟫) • K y := by
  have hK : AEStronglyMeasurable (K : Vec3 → ℂ) volume := K.continuous.aestronglyMeasurable
  rw [Real.iteratedFDeriv_fourier (N := ⊤) (fun n _ => K.integrable_pow_mul volume n) hK (by simp),
    Real.fourier_continuousMultilinearMap_apply
      (VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ)
        (K.integrable_pow_mul volume j) hK),
    Real.fourier_eq', ← integral_smul]
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, VectorFourier.fourierPowSMulRight_apply]
  rfl

/-- A Schwartz kernel whose symbol is constant near zero has all its positive
orders of signed moments equal to zero. -/
theorem integral_innerProduct_moment_eq_zero (K : 𝓢(Vec3, ℂ)) {c : ℂ}
    (hc : (𝓕 (K : Vec3 → ℂ)) =ᶠ[𝓝 (0 : Vec3)] (fun _ => c))
    {j : ℕ} (hj : 0 < j) (v : Fin j → Vec3) :
    (∫ y, (∏ i, ⟪y, v i⟫) • K y) = 0 := by
  have hz := (hc.iteratedFDeriv ℝ j).eq_of_nhds
  rw [iteratedFDeriv_const_of_ne hj.ne', Pi.zero_apply] at hz
  have hf := congrArg (fun f : (Vec3 [×j]→L[ℝ] ℂ) => f v) hz
  rw [iteratedFDeriv_fourier_schwartz_zero, zero_apply] at hf
  have hcoef : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ j ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero))
  exact (smul_eq_zero.mp hf).resolve_left hcoef

/-- Positive signed moments vanish for the dilated, actual Appendix B kernel. -/
theorem integral_scaledCutoffSchwartzKernel_innerProduct_moment_eq_zero
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {j : ℕ} (hj : 0 < j) (v : Fin j → Vec3) :
    (∫ y, (∏ i, ⟪y, v i⟫) • scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y) = 0 := by
  let K := scaledSchwartzKernel Λ hΛ.ne' (cutoffSchwartzKernel hψ hs)
  apply integral_innerProduct_moment_eq_zero K (c := 1) ?_ hj v
  filter_upwards [Metric.ball_mem_nhds (0 : Vec3) hΛ] with ξ hξ
  change (𝓕 (scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs))) ξ = 1
  rw [fourier_scaledLiftKernel hΛ, fourier_cutoffSchwartzKernel hψ hs, hunit, Complex.ofReal_one]
  change dist ξ 0 < Λ at hξ
  rw [dist_zero_right] at hξ
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le), ← div_eq_inv_mul,
    div_le_one hΛ]
  exact hξ.le

/-- The positive-degree coordinate moments include every monomial with repeated coordinate
indices. -/
theorem integral_scaledCutoffSchwartzKernel_coordinate_moment_eq_zero
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {j : ℕ} (hj : 0 < j) (ι : Fin j → Fin 3) :
    (∫ y, (∏ i, y (ι i)) • scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y) = 0 := by
  simpa only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial] using
    integral_scaledCutoffSchwartzKernel_innerProduct_moment_eq_zero hψ hs hunit hΛ hj
      (fun i => EuclideanSpace.single (ι i) 1)

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem integrable_coordinate_moment (K : 𝓢(Vec3, ℂ)) {j : ℕ} (ι : Fin j → Fin 3) :
    Integrable (fun y => (∏ i, y (ι i)) • K y) := by
  have hc : Continuous (fun y : Vec3 => (∏ i, y (ι i)) • K y) := by
    fun_prop
  refine (K.integrable_pow_mul volume j).mono' hc.aestronglyMeasurable ?_
  filter_upwards with y
  rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    (∏ i, |y (ι i)|) ≤ ∏ _ : Fin j, ‖y‖ :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => PiLp.norm_apply_le y (ι i))
    _ = ‖y‖ ^ j := by simp

private theorem multilinear_diagonal_eq_sum {j : ℕ} (A : Vec3 [×j]→L[ℝ] E) (y : Vec3) :
    A (fun _ => y) = ∑ ι : Fin j → Fin 3,
      (∏ i, y (ι i)) • A (fun i => EuclideanSpace.single (ι i) 1) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  calc
    A (fun _ => y) = A (fun _ => ∑ k : Fin 3, y k • b k) := by
      congr 1
      funext i
      exact (b.sum_repr y).symm
    _ = _ := by
      change A.toMultilinearMap (fun _ => ∑ k : Fin 3, y k • b k) = _
      rw [A.toMultilinearMap.map_sum (fun _ k => y k • b k)]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [A.toMultilinearMap.map_smul_univ]
      simp only [b, EuclideanSpace.basisFun_apply]
      rfl

private theorem integrable_smul_multilinear_diagonal (K : 𝓢(Vec3, ℂ)) {j : ℕ}
    (A : Vec3 [×j]→L[ℝ] E) :
    Integrable (fun y => K y • A (fun _ => y)) := by
  have hc : Continuous (fun y : Vec3 => K y • A (fun _ => y)) :=
    K.continuous.smul (A.cont.comp (continuous_pi (fun _ => continuous_id)))
  refine ((K.integrable_pow_mul volume j).mul_const ‖A‖).mono' hc.aestronglyMeasurable ?_
  filter_upwards with y
  change ‖K y • A (fun _ => y)‖ ≤ ‖y‖ ^ j * ‖K y‖ * ‖A‖
  rw [norm_smul, show ‖y‖ ^ j * ‖K y‖ * ‖A‖ = ‖K y‖ * (‖A‖ * ‖y‖ ^ j) by ring]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa using A.le_opNorm (fun _ => y)

/-- Coordinate moments give cancellation for every positive-degree homogeneous
Taylor term with values in a complex Banach space. -/
theorem integral_scaledCutoffSchwartzKernel_smul_multilinear_diagonal_eq_zero [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {j : ℕ} (hj : 0 < j) (A : Vec3 [×j]→L[ℝ] E) :
    (∫ y, scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y • A (fun _ => y)) = 0 := by
  let K := scaledSchwartzKernel Λ hΛ.ne' (cutoffSchwartzKernel hψ hs)
  change (∫ y, K y • A (fun _ => y)) = 0
  simp_rw [multilinear_diagonal_eq_sum, Finset.smul_sum, smul_comm (K _), ← smul_assoc]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro ι _
    rw [integral_smul_const]
    change ((∫ y, (∏ i, y (ι i)) • scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y) •
      A (fun i => EuclideanSpace.single (ι i) 1)) = 0
    rw [integral_scaledCutoffSchwartzKernel_coordinate_moment_eq_zero hψ hs hunit hΛ hj,
      zero_smul]
  · intro ι _
    exact (integrable_coordinate_moment K ι).smul_const _

private theorem iteratedDeriv_affineLine {f : Vec3 → E} {n j : ℕ} (hf : ContDiff ℝ n f)
    (hj : j ≤ n) (x y : Vec3) (t : ℝ) :
    iteratedDeriv j (fun s : ℝ => f (x + s • y)) t =
      iteratedFDeriv ℝ j f (x + t • y) (fun _ => y) := by
  let T := ContinuousLinearMap.toSpanSingleton ℝ y
  have hshift : ContDiff ℝ n (fun z => f (x + z)) := hf.comp (by fun_prop)
  change iteratedDeriv j ((fun z => f (x + z)) ∘ T) t = _
  rw [iteratedDeriv, T.iteratedFDeriv_comp_right hshift t (by exact_mod_cast hj),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp only [T, ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- The Taylor polynomial of (y mapsto f(x-y)) at phase-space displacement zero. -/
private def kernelTaylorPolynomial (f : Vec3 → E) (x : Vec3) (n : ℕ) (y : Vec3) : E :=
  ∑ j ∈ Finset.range (n + 1),
    ((j ! : ℝ)⁻¹) • iteratedFDeriv ℝ j f x (fun _ => -y)

private theorem norm_sub_kernelTaylorPolynomial_le {f : Vec3 → E} {n : ℕ}
    (hf : ContDiff ℝ (n + 1 : ℕ) f) {M : ℝ}
    (hM : ∀ z, ‖iteratedFDeriv ℝ (n + 1) f z‖ ≤ M) (x y : Vec3) :
    ‖f (x - y) - kernelTaylorPolynomial f x n y‖ ≤ M * ‖y‖ ^ (n + 1) := by
  let g (t : ℝ) := f (x + t • (-y))
  have hg : ContDiff ℝ (n + 1 : ℕ) g := hf.comp (by fun_prop)
  have hwithin (j : ℕ) (hj : j ≤ n + 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin j g (Set.Icc 0 1) t =
        iteratedFDeriv ℝ j f (x + t • (-y)) (fun _ => -y) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (hg.of_le (by exact_mod_cast hj)).contDiffAt ht]
    exact iteratedDeriv_affineLine hf hj x (-y) t
  have hTaylor : taylorWithinEval g n (Set.Icc 0 1) 0 1 = kernelTaylorPolynomial f x n y := by
    rw [taylor_within_apply, kernelTaylorPolynomial]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hwithin j (Finset.mem_range.mp hj).le (Set.left_mem_Icc.mpr zero_le_one)]
    simp
  have hnonneg := (norm_nonneg (iteratedFDeriv ℝ (n + 1) f x)).trans (hM x)
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n + 1) g (Set.Icc 0 1) t‖ ≤ M * ‖y‖ ^ (n + 1) := by
    rw [hwithin _ le_rfl ht]
    exact ((iteratedFDeriv ℝ (n + 1) f _).le_opNorm (fun _ => -y)).trans
      (by simpa only [norm_neg, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        mul_le_mul_of_nonneg_right (hM (x + t • (-y))) (pow_nonneg (norm_nonneg y) (n + 1)))
  have h := taylor_mean_remainder_bound (n := n) zero_le_one hg.contDiffOn
    (Set.right_mem_Icc.mpr zero_le_one) hbound
  simp only [g, one_smul, ← sub_eq_add_neg, hTaylor, sub_zero, one_pow, mul_one] at h
  exact h.trans (div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos n))

private theorem integrable_integral_scaledCutoffSchwartzKernel_smul_taylor [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (f : Vec3 → E) (x : Vec3) (n : ℕ) :
    Integrable (fun y => scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y •
      kernelTaylorPolynomial f x n y) ∧
    (∫ y, scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y • kernelTaylorPolynomial f x n y) =
      f x := by
  let K := scaledSchwartzKernel Λ hΛ.ne' (cutoffSchwartzKernel hψ hs)
  let B (j : ℕ) : Vec3 [×j]→L[ℝ] E :=
    ((j ! : ℝ)⁻¹) • (iteratedFDeriv ℝ j f x).compContinuousLinearMap
      (fun _ => -(ContinuousLinearMap.id ℝ Vec3))
  change Integrable (fun y => K y • ∑ j ∈ Finset.range (n + 1), B j (fun _ => y)) ∧
    (∫ y, K y • ∑ j ∈ Finset.range (n + 1), B j (fun _ => y)) = f x
  simp only [Finset.smul_sum]
  have hInt (j : ℕ) := integrable_smul_multilinear_diagonal K (B j)
  refine ⟨integrable_finsetSum _ (fun j _ => hInt j), ?_⟩
  rw [integral_finsetSum]
  · rw [Finset.sum_eq_single 0]
    · simp only [B, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
        ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_zero_apply]
      rw [integral_smul_const]
      change ((∫ y, scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs) y) • f x) = f x
      rw [integral_scaledCutoffSchwartzKernel hψ hs hΛ, hunit 0 (by simp), Complex.ofReal_one,
        one_smul]
    · intro j _ hj
      exact integral_scaledCutoffSchwartzKernel_smul_multilinear_diagonal_eq_zero
        hψ hs hunit hΛ (Nat.pos_of_ne_zero hj) (B j)
    · simp
  · exact fun j _ => hInt j

/-- Appendix B's positive-order pointwise Taylor tail for the actual convolution
cutoff, with the absolute moment of the undilated kernel as the constant. -/
theorem norm_sub_liftConvolution_scaledCutoffSchwartzKernel_le [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {f : Vec3 → E} {n : ℕ} (hf : ContDiff ℝ (n + 1 : ℕ) f)
    {M₀ M : ℝ} (hM₀ : ∀ z, ‖f z‖ ≤ M₀) (hM : ∀ z, ‖iteratedFDeriv ℝ (n + 1) f z‖ ≤ M)
    (x : Vec3) :
    ‖f x - liftConvolution (scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs)) f x‖ ≤
      (Λ⁻¹) ^ (n + 1) * (∫ y, ‖y‖ ^ (n + 1) * ‖cutoffSchwartzKernel hψ hs y‖) * M := by
  let K := scaledSchwartzKernel Λ hΛ.ne' (cutoffSchwartzKernel hψ hs)
  let P := kernelTaylorPolynomial f x n
  have hPoly : Integrable (fun y => K y • P y) ∧ (∫ y, K y • P y) = f x :=
    integrable_integral_scaledCutoffSchwartzKernel_smul_taylor hψ hs hunit hΛ f x n
  have hInt := integrable_liftConvolution (K := (K : Vec3 → ℂ)) K.integrable hf.continuous hM₀ x
  have hEq : f x - liftConvolution (K : Vec3 → ℂ) f x =
      ∫ y, K y • (P y - f (x - y)) := by
    simp only [liftConvolution, smul_sub, integral_sub hPoly.1 hInt, hPoly.2]
  rw [← integral_norm_pow_scaledLiftKernel hΛ (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) (n + 1)]
  change ‖f x - liftConvolution (K : Vec3 → ℂ) f x‖ ≤ (∫ y, ‖y‖ ^ (n + 1) * ‖K y‖) * M
  rw [hEq]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hnorm := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => norm_nonneg (K y • (P y - f (x - y))))
    ((K.integrable_pow_mul volume (n + 1)).mul_const M)
    (Filter.Eventually.of_forall fun y => by
      change ‖K y • (P y - f (x - y))‖ ≤ ‖y‖ ^ (n + 1) * ‖K y‖ * M
      rw [norm_smul, norm_sub_rev, show ‖y‖ ^ (n + 1) * ‖K y‖ * M =
        ‖K y‖ * (M * ‖y‖ ^ (n + 1)) by ring]
      exact mul_le_mul_of_nonneg_left (norm_sub_kernelTaylorPolynomial_le hf hM x y)
        (norm_nonneg _))
  rwa [integral_mul_const] at hnorm

/-- The Taylor tail estimate also holds on differences of spatial translates. -/
theorem norm_sub_liftConvolution_scaledCutoffSchwartzKernel_increment_le [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {f : Vec3 → E} {n : ℕ} (hf : ContDiff ℝ (n + 1 : ℕ) f)
    {M₀ : ℝ} (hM₀ : ∀ z, ‖f z‖ ≤ M₀) (v : Vec3) {D : ℝ}
    (hD : ∀ z, ‖iteratedFDeriv ℝ (n + 1) f (z + v) - iteratedFDeriv ℝ (n + 1) f z‖ ≤ D)
    (x : Vec3) :
    let K := scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs)
    ‖(f (x + v) - liftConvolution K f (x + v)) - (f x - liftConvolution K f x)‖ ≤
      (Λ⁻¹) ^ (n + 1) * (∫ y, ‖y‖ ^ (n + 1) * ‖cutoffSchwartzKernel hψ hs y‖) * D := by
  let K := scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs)
  let g (z : Vec3) := f (z + v) - f z
  have htranslate : ContDiff ℝ (n + 1 : ℕ) (fun z => f (z + v)) := hf.comp (by fun_prop)
  have hg : ContDiff ℝ (n + 1 : ℕ) g := htranslate.sub hf
  have hbound (z : Vec3) : ‖g z‖ ≤ 2 * M₀ := by
    calc
      _ ≤ ‖f (z + v)‖ + ‖f z‖ := norm_sub_le _ _
      _ ≤ 2 * M₀ := by linarith [hM₀ (z + v), hM₀ z]
  have hderiv (z : Vec3) : ‖iteratedFDeriv ℝ (n + 1) g z‖ ≤ D := by
    change ‖iteratedFDeriv ℝ (n + 1) ((fun z => f (z + v)) - f) z‖ ≤ D
    rw [iteratedFDeriv_sub htranslate hf]
    simp only [Pi.sub_apply, iteratedFDeriv_comp_add_right]
    exact hD z
  have hK : Integrable K := integrable_scaledLiftKernel hΛ (cutoffSchwartzKernel hψ hs).integrable
  have hdiff : liftConvolution K g x = liftConvolution K f (x + v) - liftConvolution K f x := by
    unfold liftConvolution
    have hadd (y : Vec3) : x - y + v = x + v - y := by abel
    simp only [g, hadd, smul_sub, integral_sub (integrable_liftConvolution hK hf.continuous hM₀ _)
      (integrable_liftConvolution hK hf.continuous hM₀ _)]
  have h := norm_sub_liftConvolution_scaledCutoffSchwartzKernel_le
    hψ hs hunit hΛ hg hbound hderiv x
  change ‖g x - liftConvolution K g x‖ ≤ _ at h
  rw [hdiff] at h
  convert h using 2
  dsimp only [g]
  abel

end Taylor

end

end TorusEuler
