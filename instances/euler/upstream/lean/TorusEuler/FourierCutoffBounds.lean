import TorusEuler.FourierKernelMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Differentiation and Bernstein estimates for the lift cutoff of Appendix B. -/

open MeasureTheory Filter UnitAddTorus LineDeriv
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap Topology

namespace TorusEuler

noncomputable section

section Differentiation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bounded first derivative can pass through the lift convolution. -/
theorem fderiv_liftConvolution_eq_liftConvolution_fderiv
    {K : Vec3 → ℂ} (hK : Integrable K) {f : Vec3 → E} (hf : ContDiff ℝ 1 f)
    {M M' : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (hM' : ∀ z, ‖fderiv ℝ f z‖ ≤ M')
    (x : Vec3) :
    fderiv ℝ (liftConvolution K f) x = liftConvolution K (fderiv ℝ f) x := by
  have hc := hf.continuous_fderiv (by norm_num)
  change fderiv ℝ (fun z => ∫ y, K y • f (z - y)) x = ∫ y, K y • fderiv ℝ f (x - y)
  apply HasFDerivAt.fderiv
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume) (F := fun z y => K y • f (z - y))
    (F' := fun z y => K y • fderiv ℝ f (z - y))
    (s := Set.univ) (bound := fun y => ‖K y‖ * M') Filter.univ_mem
  · exact Eventually.of_forall fun z => (integrable_liftConvolution hK hf.continuous hM z).1
  · exact integrable_liftConvolution hK hf.continuous hM x
  · exact (integrable_liftConvolution hK hc hM' x).1
  · exact Eventually.of_forall fun y z _ => by
      change ‖K y • fderiv ℝ f (z - y)‖ ≤ ‖K y‖ * M'
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM' _) (norm_nonneg _)
  · exact hK.norm.mul_const _
  · refine Eventually.of_forall fun y z _ => ?_
    have h := ((hf.differentiable (by norm_num) (z - y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const y)).const_smul (K y)
    have he : (K y • (f ∘ fun x => id x - y) : Vec3 → E) = (fun x => K y • f (x - y)) :=
      funext fun _ => rfl
    rwa [ContinuousLinearMap.comp_id, he] at h

/-- Each bounded derivative through order `j` commutes with convolution by
the integrable lift kernel. -/
theorem iteratedFDeriv_liftConvolution_eq_liftConvolution_iteratedFDeriv [CompleteSpace E]
    {K : Vec3 → ℂ} (hK : Integrable K) {f : Vec3 → E} {j : ℕ} (hf : ContDiff ℝ j f)
    (M : ℕ → ℝ) (hM : ∀ n ≤ j, ∀ z, ‖iteratedFDeriv ℝ n f z‖ ≤ M n) :
    iteratedFDeriv ℝ j (liftConvolution K f) = liftConvolution K (iteratedFDeriv ℝ j f) := by
  induction j with
  | zero =>
    funext x
    ext v
    rw [iteratedFDeriv_zero_apply]
    unfold liftConvolution
    rw [ContinuousMultilinearMap.integral_apply (integrable_liftConvolution hK
      (hf.continuous_iteratedFDeriv le_rfl) (hM 0 le_rfl) x)]
    rfl
  | succ j ih =>
    have hj : (j : ℕ∞ω) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
    have hc : ContDiff ℝ 1 (iteratedFDeriv ℝ j f) :=
      hf.iteratedFDeriv_right (by norm_cast; omega)
    have hbound (z : Vec3) : ‖fderiv ℝ (iteratedFDeriv ℝ j f) z‖ ≤ M (j + 1) := by
      rw [norm_fderiv_iteratedFDeriv]
      exact hM (j + 1) le_rfl z
    have hsmall := hM j (Nat.le_succ _)
    funext x
    ext v
    rw [iteratedFDeriv_succ_apply_left, ih (hf.of_le hj) (fun n hn => hM n (hn.trans (Nat.le_succ _))),
      fderiv_liftConvolution_eq_liftConvolution_fderiv hK hc hsmall hbound]
    unfold liftConvolution
    have hInt := integrable_liftConvolution hK (hc.continuous_fderiv (by norm_num)) hbound x
    rw [ContinuousLinearMap.integral_apply hInt (v 0)]
    have hEval : Integrable
        (fun y => (K y • fderiv ℝ (iteratedFDeriv ℝ j f) (x - y)) (v 0)) :=
      (ContinuousLinearMap.apply ℝ (Vec3 [×j]→L[ℝ] E) (v 0)).integrable_comp hInt
    rw [ContinuousMultilinearMap.integral_apply hEval (Fin.tail v),
      ContinuousMultilinearMap.integral_apply
        (integrable_liftConvolution hK (hf.continuous_iteratedFDeriv (by norm_cast))
          (hM (j + 1) le_rfl) x)]
    rfl

end Differentiation

private def kernelDirectionSymbol (ξ v : Vec3) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) * (⟪ξ, v⟫ : ℝ)

private theorem fourier_lineDerivOp_kernel (K : 𝓢(Vec3, ℂ)) (ξ v : Vec3) :
    (𝓕 ((∂_{v} K : 𝓢(Vec3, ℂ)) : Vec3 → ℂ)) ξ =
      kernelDirectionSymbol ξ v * (𝓕 (K : Vec3 → ℂ)) ξ := by
  rw [← SchwartzMap.fourier_coe, SchwartzMap.fourier_lineDerivOp_eq]
  have h : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply h,
    SchwartzMap.fourier_coe, kernelDirectionSymbol, smul_eq_mul, Complex.real_smul, mul_assoc]

private theorem fourier_iteratedKernelDerivative (K : 𝓢(Vec3, ℂ)) {j : ℕ} (v : Fin j → Vec3)
    (ξ : Vec3) :
    (𝓕 ((∂^{v} K : 𝓢(Vec3, ℂ)) : Vec3 → ℂ)) ξ =
      (∏ i, kernelDirectionSymbol ξ (v i)) * (𝓕 (K : Vec3 → ℂ)) ξ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedLineDerivOp_succ_left, fourier_lineDerivOp_kernel, ih, Fin.prod_univ_succ, mul_assoc]
    rfl

private theorem fderiv_fourierMode_symbol (k : Fin 3 → ℤ) (x v : Vec3) :
    fderiv ℝ (fourierMode k) x v =
      kernelDirectionSymbol (latticeVector k) v * fourierMode k x := by
  rw [fderiv_fourierMode, kernelDirectionSymbol]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, latticeVector, mul_comm]

private theorem lineDeriv_lift_finiteFourierSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) (x v : Vec3) :
    fderiv ℝ (fun z => finiteFourierSum s a (toUnitTorus z)) x v =
      finiteFourierSum s (fun k => kernelDirectionSymbol (latticeVector k) v • a k) (toUnitTorus x) := by
  change fderiv ℝ (fun z => ∑ k ∈ s, fourierMode k z • a k) x v =
    ∑ k ∈ s, fourierMode k x • (kernelDirectionSymbol (latticeVector k) v • a k)
  have hmode k := ((contDiff_fourierMode k).differentiable (by simp) x).hasFDerivAt
  have hd := HasFDerivAt.fun_sum (u := s) (fun k _ => (hmode k).smul_const (a k))
  rw [hd.fderiv, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, fderiv_fourierMode_symbol, ← smul_smul]
  exact smul_comm _ _ _

/-- Iterated spatial derivatives on an arbitrary finite Fourier synthesis. -/
theorem iteratedFDeriv_lift_finiteFourierSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) {j : ℕ}
    (v : Fin j → Vec3) (x : Vec3) :
    iteratedFDeriv ℝ j (fun z => finiteFourierSum s a (toUnitTorus z)) x v =
      finiteFourierSum s (fun k => (∏ i, kernelDirectionSymbol (latticeVector k) (v i)) • a k)
        (toUnitTorus x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedFDeriv_succ_apply_left v, ← fderiv_continuousMultilinear_apply_const_apply]
    · have htail := funext (ih (Fin.tail v))
      rw [htail, lineDeriv_lift_finiteFourierSum]
      unfold finiteFourierSum
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only
      congr 1
      rw [smul_smul, Fin.prod_univ_succ]
      rfl
    · exact ((contDiff_lift_finiteFourierSum s a).differentiable_iteratedFDeriv
        (mod_cast ENat.natCast_lt_top j)) x

/-- On trigonometric polynomials, every spatial derivative of a Schwartz convolution
is exactly the convolution with the corresponding derivative of its kernel. -/
theorem iteratedFDeriv_liftConvolution_finiteFourierSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (K : 𝓢(Vec3, ℂ)) (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → E) {j : ℕ} (v : Fin j → Vec3) (x : Vec3) :
    iteratedFDeriv ℝ j (liftConvolution (K : Vec3 → ℂ)
      (fun z => finiteFourierSum s a (toUnitTorus z))) x v =
      liftConvolution ((∂^{v} K : 𝓢(Vec3, ℂ)) : Vec3 → ℂ)
        (fun z => finiteFourierSum s a (toUnitTorus z)) x := by
  rw [funext (liftConvolution_lift_finiteFourierSum K.integrable s a),
    iteratedFDeriv_lift_finiteFourierSum, liftConvolution_lift_finiteFourierSum (∂^{v} K).integrable]
  unfold finiteFourierSum
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [fourier_iteratedKernelDerivative]
  congr 1
  exact smul_smul _ _ _

/-- The (L^1) norm of an iterated derivative of the dilated kernel scales as (Lambda^j). -/
theorem integral_norm_iteratedFDeriv_scaledLiftKernel {Λ : ℝ} (hΛ : 0 < Λ)
    (K : 𝓢(Vec3, ℂ)) {j : ℕ} (v : Fin j → Vec3) :
    (∫ y, ‖iteratedFDeriv ℝ j (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v‖) =
      Λ ^ j * ∫ y, ‖iteratedFDeriv ℝ j (K : Vec3 → ℂ) y v‖ := by
  have hderiv (y : Vec3) :
      iteratedFDeriv ℝ j (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v =
        Λ ^ j • scaledLiftKernel Λ (fun z => iteratedFDeriv ℝ j (K : Vec3 → ℂ) z v) y := by
    have hc : ContDiff ℝ j (fun z : Vec3 => K (Λ • z)) :=
      (K.smooth j).comp (by fun_prop)
    unfold scaledLiftKernel
    rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt, iteratedFDeriv_comp_const_smul Λ (K.smooth j)]
    simp only [smul_apply, smul_comm (Λ ^ (3 : ℕ))]
  simp_rw [hderiv, norm_smul, Real.norm_of_nonneg (pow_nonneg hΛ.le j)]
  rw [integral_const_mul, integral_norm_scaledLiftKernel hΛ]

/-- Bernstein's estimate, stated for each derivative direction list and each
band-limited trigonometric polynomial. The constant is the corresponding
undilated kernel derivative's (L^1) norm times (4^j). -/
theorem bernstein_lift_finiteFourierSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hψsmooth : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {s : Finset (Fin 3 → ℤ)} (hs : s ⊆ frequencyBand (4 * Λ))
    (a : (Fin 3 → ℤ) → E) {M : ℝ}
    (hM : ∀ x, ‖finiteFourierSum s a (toUnitTorus x)‖ ≤ M)
    {j : ℕ} (v : Fin j → Vec3) (x : Vec3) :
    ‖iteratedFDeriv ℝ j (fun z => finiteFourierSum s a (toUnitTorus z)) x v‖ ≤
      (4 * Λ) ^ j * (∫ y, ‖iteratedFDeriv ℝ j
        (cutoffSchwartzKernel hψ hψsmooth : Vec3 → ℂ) y v‖) * M := by
  let R := 4 * Λ
  have hR : 0 < R := by positivity
  let K := cutoffSchwartzKernel hψ hψsmooth
  let KR := scaledSchwartzKernel R hR.ne' K
  let f := fun z => finiteFourierSum s a (toUnitTorus z)
  have hrep : liftConvolution (KR : Vec3 → ℂ) f = f := by
    funext z
    change liftConvolution (scaledLiftKernel R K) f z = f z
    rw [liftConvolution_lift_finiteFourierSum (integrable_scaledLiftKernel hR K.integrable)]
    unfold f finiteFourierSum
    refine Finset.sum_congr rfl fun k hk => ?_
    dsimp only
    have hscaled : ‖R⁻¹ • latticeVector k‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), ← div_eq_inv_mul,
        div_le_one hR]
      exact (mem_frequencyBand _ _).mp (hs hk)
    rw [fourier_scaledLiftKernel hR, fourier_cutoffSchwartzKernel hψ hψsmooth,
      hunit _ hscaled, Complex.ofReal_one, one_smul]
  change ‖iteratedFDeriv ℝ j f x v‖ ≤ _
  conv_lhs => rw [← hrep, iteratedFDeriv_liftConvolution_finiteFourierSum]
  have h := norm_liftConvolution_le (∂^{v} KR).integrable hM x
  simp_rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv] at h
  have hscale := integral_norm_iteratedFDeriv_scaledLiftKernel hR K v
  change (∫ y, ‖iteratedFDeriv ℝ j (KR : Vec3 → ℂ) y v‖) = _ at hscale
  rwa [hscale] at h

section TorusConvolution

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem toUnitTorus_sub (x y : Vec3) :
    toUnitTorus (x - y) = toUnitTorus x - toUnitTorus y := by
  funext i
  exact AddCircle.coe_sub 1 (x i) (y i)

private theorem continuous_toUnitTorus : Continuous toUnitTorus :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)

private theorem mFourier_add_arg (k : Fin 3 → ℤ) (z w : UnitAddTorus (Fin 3)) :
    mFourier k (z + w) = mFourier k z * mFourier k w := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private theorem fourier_eq_integral_mode (K : Vec3 → ℂ) (k : Fin 3 → ℤ) :
    (𝓕 K) (latticeVector k) = ∫ y, mFourier (-k) (toUnitTorus y) * K y := by
  have hzero : fourierMode k 0 = 1 := by simp [fourierMode_eq_exp]
  calc
    _ = liftConvolution K (fourierMode k) 0 := by rw [liftConvolution_fourierMode, hzero, mul_one]
    _ = _ := by
      unfold liftConvolution
      congr 1
      funext y
      rw [zero_sub, fourierMode, show toUnitTorus (-y) = -toUnitTorus y by
        rw [← zero_sub, toUnitTorus_sub]
        have : toUnitTorus 0 = 0 := by ext i; simp [toUnitTorus]
        rw [this, zero_sub], mFourier_neg_arg, smul_eq_mul, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Convolution against an integrable Euclidean kernel, evaluated on the torus by
subtracting the image of each Euclidean integration variable. -/
def torusLiftConvolution (K : Vec3 → ℂ) (hK : Integrable K) (g : C(UnitAddTorus (Fin 3), E)) :
    C(UnitAddTorus (Fin 3), E) where
  toFun z := ∫ y, K y • g (z - toUnitTorus y)
  continuous_toFun := by
    refine continuous_of_dominated (bound := fun y => ‖K y‖ * ‖g‖) ?_ ?_ (hK.norm.mul_const _) ?_
    · exact fun z => hK.aestronglyMeasurable.smul
        (g.continuous.comp (continuous_const.sub continuous_toUnitTorus)).aestronglyMeasurable
    · exact fun z => Eventually.of_forall fun y => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _)
    · exact Eventually.of_forall fun y =>
        (g.continuous.comp (continuous_id.sub continuous_const)).const_smul _

omit [CompleteSpace E] in
theorem torusLiftConvolution_toUnitTorus (K : Vec3 → ℂ) (hK : Integrable K)
    (g : C(UnitAddTorus (Fin 3), E)) (x : Vec3) :
    torusLiftConvolution K hK g (toUnitTorus x) =
      liftConvolution K (fun z => g (toUnitTorus z)) x := by
  simp only [torusLiftConvolution, ContinuousMap.coe_mk, liftConvolution, toUnitTorus_sub]

theorem mFourierCoeff_torusLiftConvolution (K : 𝓢(Vec3, ℂ))
    (g : C(UnitAddTorus (Fin 3), E)) (k : Fin 3 → ℤ) :
    mFourierCoeff (torusLiftConvolution (K : Vec3 → ℂ) K.integrable g) k =
      (𝓕 (K : Vec3 → ℂ)) (latticeVector k) • mFourierCoeff g k := by
  let H (z : UnitAddTorus (Fin 3)) (y : Vec3) :=
    mFourier (-k) z • (K y • g (z - toUnitTorus y))
  have hcont : Continuous (Function.uncurry H) :=
    ((mFourier (-k)).continuous.comp continuous_fst).smul
      ((K.continuous.comp continuous_snd).smul
        (g.continuous.comp (continuous_fst.sub (continuous_toUnitTorus.comp continuous_snd))))
  have hint : Integrable (Function.uncurry H) (volume.prod volume) := by
    refine ((K.integrable.norm.comp_snd (volume : Measure (UnitAddTorus (Fin 3)))).mul_const ‖g‖).mono'
      hcont.aestronglyMeasurable ?_
    filter_upwards with p
    change ‖mFourier (-k) p.1 • (K p.2 • g (p.1 - toUnitTorus p.2))‖ ≤ ‖K p.2‖ * ‖g‖
    rw [norm_smul, norm_smul]
    refine mul_le_of_le_one_left (by positivity) ?_ |>.trans ?_
    · simpa only [mFourier_norm] using (mFourier (-k)).norm_coe_le_norm p.1
    · exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _)
  rw [fourier_eq_integral_mode]
  simp only [mFourierCoeff, torusLiftConvolution, ContinuousMap.coe_mk]
  have hL : (∫ z, mFourier (-k) z • ∫ y, K y • g (z - toUnitTorus y)) =
      ∫ z, ∫ y, H z y := by
    apply integral_congr_ae
    filter_upwards with z
    exact (integral_smul (mFourier (-k) z) (fun y => K y • g (z - toUnitTorus y))).symm
  rw [hL, integral_integral_swap hint, ← integral_smul_const]
  congr 1
  funext y
  rw [← integral_add_right_eq_self (H · y) (toUnitTorus y)]
  simp only [H, add_sub_cancel_right, mFourier_add_arg]
  rw [← integral_smul]
  congr 1
  funext z
  simp only [smul_smul]
  congr 1
  ring

private theorem eq_of_mFourierCoeff_eq_complex (u w : C(UnitAddTorus (Fin 3), ℂ))
    (h : ∀ k, mFourierCoeff u k = mFourierCoeff w k) : u = w := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) volume
  apply mFourierBasis.repr.injective
  ext k
  rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_toLp, mFourierCoeff_toLp, h]

private theorem mFourierCoeff_comp_clm (L : E →L[ℂ] ℂ) (g : C(UnitAddTorus (Fin 3), E))
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun z => L (g z)) k = L (mFourierCoeff g k) := by
  have hint : Integrable (fun z => mFourier (-k) z • g z) :=
    ((mFourier (-k)).continuous.smul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold mFourierCoeff
  rw [← L.integral_comp_comm hint]
  simp only [map_smul]

/-- Fourier coefficients characterize every continuous Banach-valued field on the unit torus. -/
theorem eq_of_mFourierCoeff_eq (u w : C(UnitAddTorus (Fin 3), E))
    (h : ∀ k, mFourierCoeff u k = mFourierCoeff w k) : u = w := by
  ext z
  by_contra! hne
  obtain ⟨L, _, hL⟩ := exists_dual_vector ℂ (u z - w z) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  let u' : C(UnitAddTorus (Fin 3), ℂ) := ⟨L ∘ u, L.continuous.comp u.continuous⟩
  let w' : C(UnitAddTorus (Fin 3), ℂ) := ⟨L ∘ w, L.continuous.comp w.continuous⟩
  have heq := eq_of_mFourierCoeff_eq_complex u' w' (fun k => by
    change mFourierCoeff (fun z => L (u z)) k = mFourierCoeff (fun z => L (w z)) k
    rw [mFourierCoeff_comp_clm, mFourierCoeff_comp_clm, h])
  have hz : L (u z) = L (w z) := congrArg (fun f : C(UnitAddTorus (Fin 3), ℂ) => f z) heq
  rw [map_sub, hz, sub_self] at hL
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hL.symm)))

omit [CompleteSpace E] in
private theorem continuous_finiteFourierSum (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) :
    Continuous (finiteFourierSum s a) := by
  unfold finiteFourierSum
  exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const

/-- The physical Schwartz convolution realizes the smooth spectral cutoff of
Appendix B for every continuous torus field. -/
theorem liftConvolution_cutoffSchwartzKernel
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    {Λ : ℝ} (hΛ : 0 < Λ) (g : C(UnitAddTorus (Fin 3), E)) (x : Vec3) :
    liftConvolution (scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs))
      (fun z => g (toUnitTorus z)) x = smoothFourierCutoff ψ Λ g (toUnitTorus x) := by
  let K := scaledSchwartzKernel Λ hΛ.ne' (cutoffSchwartzKernel hψ hs)
  let w : C(UnitAddTorus (Fin 3), E) := ⟨smoothFourierCutoff ψ Λ g, continuous_finiteFourierSum _ _⟩
  have h : torusLiftConvolution (K : Vec3 → ℂ) K.integrable g = w := by
    apply eq_of_mFourierCoeff_eq
    intro k
    rw [mFourierCoeff_torusLiftConvolution]
    change (𝓕 (scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs))) (latticeVector k) •
      mFourierCoeff g k = mFourierCoeff (smoothFourierCutoff ψ Λ g) k
    rw [fourier_scaledLiftKernel hΛ, fourier_cutoffSchwartzKernel hψ hs,
      mFourierCoeff_smoothFourierCutoff hΛ hψ, Complex.coe_smul]
  change liftConvolution (K : Vec3 → ℂ) (fun z => g (toUnitTorus z)) x = w (toUnitTorus x)
  rw [← torusLiftConvolution_toUnitTorus (K : Vec3 → ℂ) K.integrable, h]

/-- On arbitrary continuous torus fields, differentiation of the cutoff is
convolution with the corresponding derivative of its dilated kernel. -/
theorem iteratedFDeriv_liftConvolution_cutoffSchwartzKernel
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    {Λ : ℝ} (hΛ : 0 < Λ) (g : C(UnitAddTorus (Fin 3), E))
    {j : ℕ} (v : Fin j → Vec3) (x : Vec3) :
    iteratedFDeriv ℝ j (fun z => smoothFourierCutoff ψ Λ g (toUnitTorus z)) x v =
      liftConvolution (fun y => iteratedFDeriv ℝ j
        (scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs)) y v)
        (fun z => g (toUnitTorus z)) x := by
  let K := scaledSchwartzKernel Λ hΛ.ne' (cutoffSchwartzKernel hψ hs)
  let DK := ∂^{v} K
  let a (k : Fin 3 → ℤ) : E := ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff g k
  let b (k : Fin 3 → ℤ) : E := (∏ i, kernelDirectionSymbol (latticeVector k) (v i)) • a k
  let s := frequencyBand (2 * Λ)
  let w : C(UnitAddTorus (Fin 3), E) := ⟨finiteFourierSum s b, continuous_finiteFourierSum s b⟩
  have hc : torusLiftConvolution (DK : Vec3 → ℂ) DK.integrable g = w := by
    apply eq_of_mFourierCoeff_eq
    intro k
    rw [mFourierCoeff_torusLiftConvolution]
    change (𝓕 (DK : Vec3 → ℂ)) (latticeVector k) • mFourierCoeff g k =
      mFourierCoeff (finiteFourierSum s b) k
    rw [mFourierCoeff_finiteFourierSum]
    change (𝓕 ((∂^{v} K : 𝓢(Vec3, ℂ)) : Vec3 → ℂ)) (latticeVector k) • mFourierCoeff g k = _
    rw [fourier_iteratedKernelDerivative]
    change ((∏ i, kernelDirectionSymbol (latticeVector k) (v i)) *
      (𝓕 (scaledLiftKernel Λ (cutoffSchwartzKernel hψ hs))) (latticeVector k)) •
      mFourierCoeff g k = _
    rw [fourier_scaledLiftKernel hΛ, fourier_cutoffSchwartzKernel hψ hs, mul_smul, Complex.coe_smul]
    by_cases hk : k ∈ s
    · exact (ite_eq_left hk).symm
    · have hscaled : 2 < ‖Λ⁻¹ • latticeVector k‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le), ← div_eq_inv_mul,
          lt_div_iff₀ hΛ]
        exact lt_of_not_ge (fun h => hk ((mem_frequencyBand _ _).mpr h))
      rw [hψ _ hscaled, zero_smul, smul_zero, ite_eq_right hk]
  change iteratedFDeriv ℝ j (fun z => finiteFourierSum s a (toUnitTorus z)) x v = _
  rw [iteratedFDeriv_lift_finiteFourierSum]
  have hDK : (fun y => iteratedFDeriv ℝ j (K : Vec3 → ℂ) y v) = (DK : Vec3 → ℂ) :=
    funext fun _ => SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm
  change finiteFourierSum s b (toUnitTorus x) =
    liftConvolution (fun y => iteratedFDeriv ℝ j (K : Vec3 → ℂ) y v)
      (fun z => g (toUnitTorus z)) x
  rw [hDK]
  exact (congrArg (fun g : C(UnitAddTorus (Fin 3), E) => g (toUnitTorus x)) hc).symm.trans
    (torusLiftConvolution_toUnitTorus (DK : Vec3 → ℂ) DK.integrable g x)

/-- A continuous torus field supported in a finite Fourier band has the
corresponding finite synthesis. -/
theorem finiteFourierSum_mFourierCoeff_eq_of_band
    (g : C(UnitAddTorus (Fin 3), E)) (R : ℝ)
    (hband : ∀ k, R < ‖latticeVector k‖ → mFourierCoeff g k = 0) :
    finiteFourierSum (frequencyBand R) (mFourierCoeff g) = g := by
  let w : C(UnitAddTorus (Fin 3), E) :=
    ⟨finiteFourierSum (frequencyBand R) (mFourierCoeff g), continuous_finiteFourierSum _ _⟩
  change (w : UnitAddTorus (Fin 3) → E) = g
  congr 1
  apply eq_of_mFourierCoeff_eq
  intro k
  change mFourierCoeff (finiteFourierSum _ _) k = mFourierCoeff g k
  rw [mFourierCoeff_finiteFourierSum]
  by_cases hk : k ∈ frequencyBand R
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, hband k (lt_of_not_ge (fun h => hk ((mem_frequencyBand R k).mpr h)))]

/-- The directional Bernstein bound on every continuous torus field supported
on frequencies at most \(4\Lambda\). -/
theorem bernstein_lift_of_band
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), E))
    (hband : ∀ k, 4 * Λ < ‖latticeVector k‖ → mFourierCoeff g k = 0)
    {j : ℕ} (v : Fin j → Vec3) (x : Vec3) :
    ‖iteratedFDeriv ℝ j (fun z => g (toUnitTorus z)) x v‖ ≤
      (4 * Λ) ^ j * (∫ y, ‖iteratedFDeriv ℝ j
        (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y v‖) * ‖g‖ := by
  have heq := finiteFourierSum_mFourierCoeff_eq_of_band g (4 * Λ) hband
  apply le_trans ?_ (bernstein_lift_finiteFourierSum hψ hs hunit hΛ
    (fun _ h => h) (mFourierCoeff g) (fun z => by rw [heq]; exact g.norm_coe_le_norm _) v x)
  rw [heq]

/-- Summing the coordinate-direction suprema gives a Bernstein bound with a
constant that depends only on the derivative order and the symbol. -/
theorem bernstein_lift_coordinate_sum_of_band
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), E))
    (hband : ∀ k, 4 * Λ < ‖latticeVector k‖ → mFourierCoeff g k = 0)
    (j : ℕ) :
    (∑ β : Fin j → Fin 3, ⨆ x : Vec3,
      ‖iteratedFDeriv ℝ j (fun z => g (toUnitTorus z)) x
        (fun i => EuclideanSpace.single (β i) 1)‖) ≤
      ((4 : ℝ) ^ j * ∑ β : Fin j → Fin 3, ∫ y,
        ‖iteratedFDeriv ℝ j (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y
          (fun i => EuclideanSpace.single (β i) 1)‖) * Λ ^ j * ‖g‖ := by
  let b (β : Fin j → Fin 3) :=
    ∫ y, ‖iteratedFDeriv ℝ j (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y
      (fun i => EuclideanSpace.single (β i) 1)‖
  calc
    _ ≤ ∑ β : Fin j → Fin 3, (4 * Λ) ^ j * b β * ‖g‖ := by
      apply Finset.sum_le_sum
      intro β _
      exact ciSup_le (bernstein_lift_of_band hψ hs hunit hΛ g hband
        (fun i => EuclideanSpace.single (β i) 1))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, mul_pow]; ring

end TorusConvolution

end

end TorusEuler
