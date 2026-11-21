import Breakdown.Uniqueness.RegPhysAuxBasic

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal

theorem integrable_weight_smul {f : Space → CSpace} {k : ℕ} (hf : MemLp f 1 (weightL1Measure k)) :
    Integrable (fun ξ : Space => ((1 + ‖ξ‖) ^ k) • f ξ) := by
  have hw : Measurable (fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ k)) := by fun_prop
  have h1 : Integrable f (weightL1Measure k) := memLp_one_iff_integrable.1 hf
  rw [weightL1Measure, integrable_withDensity_iff_integrable_smul' hw
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (by positivity)]

theorem aestronglyMeasurable_of_weight {f : Space → CSpace} {k : ℕ}
    (hf : MemLp f 1 (weightL1Measure k)) : AEStronglyMeasurable f volume := by
  have h := (integrable_weight_smul hf).aestronglyMeasurable
  have hc : Continuous (fun ξ : Space => ((1 + ‖ξ‖) ^ k)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun ξ => by positivity)
  refine (hc.aestronglyMeasurable.smul h).congr (Eventually.of_forall fun ξ => ?_)
  show ((1 + ‖ξ‖) ^ k)⁻¹ • ((1 + ‖ξ‖) ^ k • f ξ) = f ξ
  rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

theorem integrable_pow_mul_of_weight {f : Space → CSpace} {k : ℕ}
    (hf : MemLp f 1 (weightL1Measure k)) {n : ℕ} (hn : n ≤ k) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ n * ‖f ξ‖) := by
  have h := (integrable_weight_smul hf).norm
  refine h.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul
    (aestronglyMeasurable_of_weight hf).norm) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity), norm_smul, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖ξ‖ ^ n ≤ (1 + ‖ξ‖) ^ n := by gcongr; linarith
    _ ≤ (1 + ‖ξ‖) ^ k := pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hn

theorem integrable_of_weight {f : Space → CSpace} {k : ℕ} (hf : MemLp f 1 (weightL1Measure k)) :
    Integrable f := by
  have h := integrable_pow_mul_of_weight hf (Nat.zero_le k)
  simp only [pow_zero, one_mul] at h
  exact (integrable_norm_iff (aestronglyMeasurable_of_weight hf)).1 h

theorem toLinearMap₁₂_neg_innerSL :
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ = -innerₗ Space := by
  ext v w
  simp

theorem freqTrInv_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Space → E) (x : Space) :
    𝓕⁻ f x = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ f x := by
  rw [toLinearMap₁₂_neg_innerSL]
  rfl

theorem freqTrSMulRight_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Space → E) (v h : Space) :
    VectorFourier.fourierSMulRight (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f v h =
      (2 * (π : ℂ) * Complex.I * ((inner ℝ v h : ℝ) : ℂ)) • f v := by
  rw [VectorFourier.fourierSMulRight_apply]
  simp only [neg_apply]
  rw [innerSL_apply_apply, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

theorem integrable_freqTrSMulRight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Space → E} (hf : Integrable f) (hf' : Integrable (fun v : Space => ‖v‖ * ‖f v‖)) :
    Integrable (fun v => VectorFourier.fourierSMulRight
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f v) := by
  refine (hf'.const_mul (2 * π * ‖(-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ)‖)).mono'
    hf.1.fourierSMulRight (Eventually.of_forall fun v => ?_)
  exact (VectorFourier.norm_fourierSMulRight_le _ f v).trans (le_of_eq (by ring))

theorem integrable_symbol_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Space → E} (hf : Integrable f) (hf' : Integrable (fun v : Space => ‖v‖ * ‖f v‖))
    (h : Space) :
    Integrable (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) := by
  have := (ContinuousLinearMap.apply ℝ E h).integrable_comp (integrable_freqTrSMulRight hf hf')
  refine this.congr (Eventually.of_forall fun v => ?_)
  exact freqTrSMulRight_apply_eq f v h

theorem hasFDerivAt_freqTrInv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Space → E} (hf : Integrable f) (hf' : Integrable (fun v : Space => ‖v‖ * ‖f v‖))
    (x : Space) :
    HasFDerivAt (𝓕⁻ f) (VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂
      (VectorFourier.fourierSMulRight (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f) x) x := by
  have : 𝓕⁻ f = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ f :=
    funext fun y => freqTrInv_eq_integral f y
  rw [this]
  exact VectorFourier.hasFDerivAt_fourierIntegral _ hf hf' x

theorem freqTrIntegral_smulRight_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Space → E} (hf : Integrable f) (hf' : Integrable (fun v : Space => ‖v‖ * ‖f v‖))
    (x h : Space) :
    VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂
      (VectorFourier.fourierSMulRight (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f) x h =
      𝓕⁻ (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) x := by
  rw [VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar
    (integrable_freqTrSMulRight hf hf'), freqTrInv_eq_integral]
  congr 1
  funext v
  exact freqTrSMulRight_apply_eq f v h

theorem integrable_freqTr_integrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Space → E} (hf : Integrable f) (x : Space) :
    Integrable (fun v => 𝐞 (-((-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ v x)) • f v) :=
  (VectorFourier.fourierIntegral_convergent_iff continuous_fourierChar
    (by apply (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).continuous₂ :
      Continuous (fun p : Space × Space =>
        (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ p.1 p.2)) x).2 hf

theorem freqTrInv_coord {F : Space → CSpace} (hF : Integrable F) (x : Space) (j : Fin 3) :
    𝓕⁻ F x j = 𝓕⁻ (fun ξ => F ξ j) x := by
  rw [freqTrInv_eq_integral, freqTrInv_eq_integral]
  simp only [VectorFourier.fourierIntegral]
  change EuclideanSpace.proj (𝕜 := ℂ) j (∫ v, _) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_freqTr_integrand hF x)]
  congr 1

theorem inner_unitVector (v : Space) (i : Fin 3) : inner ℝ v (unitVector i) = v i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem sum_inner_unitVector_sq (v : Space) :
    ∑ i : Fin 3, inner ℝ v (unitVector i) * inner ℝ v (unitVector i) = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_unitVector]
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_three]
  ring

theorem sum_smul_unitVector_apply (a : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i, a i • unitVector i) j = a j := by
  simp [unitVector, Pi.single_apply]

theorem norm_freqVec (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [freqVec, complexifyVec, EuclideanSpace.norm_eq]

end Internal

open Internal in
theorem fderiv_freqTrInv_apply {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 1)) (x : Space) :
    DifferentiableAt ℝ (𝓕⁻ f) x ∧ ∀ h : Space, fderiv ℝ (𝓕⁻ f) x h =
      𝓕⁻ (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) x := by
  have h0 := integrable_of_weight hf
  have h1 : Integrable (fun v : Space => ‖v‖ * ‖f v‖) := by
    simpa using integrable_pow_mul_of_weight hf (le_refl 1)
  have hd := hasFDerivAt_freqTrInv h0 h1 x
  exact ⟨hd.differentiableAt, fun h => by rw [hd.fderiv]; exact freqTrIntegral_smulRight_apply h0 h1 x h⟩

theorem fderiv_physField_apply {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 1)) (x h : Space) :
    fderiv ℝ (physField f) x h =
      physField (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) x := by
  obtain ⟨hd, he⟩ := fderiv_freqTrInv_apply hf x
  have hc := realVec.hasFDerivAt.comp x hd.hasFDerivAt
  show fderiv ℝ (realVec ∘ 𝓕⁻ f) x h =
    realVec (𝓕⁻ (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • f ξ) x)
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, he h]

open Internal in
theorem sumSecondPartialsAt_physField {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 2)) (x : Space) :
    sumSecondPartialsAt (physField f) x = physField (sspSymbol f) x := by
  have hmeas := aestronglyMeasurable_of_weight hf
  have hpow : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (fun v : Space => ‖v‖ ^ n * ‖f v‖) :=
    fun n hn => integrable_pow_mul_of_weight hf (by exact_mod_cast hn)
  have hF : 𝓕⁻ f = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ f :=
    funext fun y => freqTrInv_eq_integral f y
  have hcd := VectorFourier.contDiff_fourierIntegral (μ := volume)
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) (N := 2) hpow
  rw [← hF] at hcd
  have hit : iteratedFDeriv ℝ 2 (𝓕⁻ f) x = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂
      (fun v => VectorFourier.fourierPowSMulRight
        (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f v 2) x := by
    rw [hF, VectorFourier.iteratedFDeriv_fourierIntegral _ hpow hmeas le_rfl]
  have hcomp : iteratedFDeriv ℝ 2 (realVec ∘ 𝓕⁻ f) x =
      realVec.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 (𝓕⁻ f) x) :=
    realVec.iteratedFDeriv_comp_left hcd.contDiffAt (by exact_mod_cast le_rfl)
  have hint := VectorFourier.integrable_fourierPowSMulRight (μ := volume)
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) (hpow 2 le_rfl) hmeas
  have hphys : physField f = realVec ∘ 𝓕⁻ f := rfl
  unfold sumSecondPartialsAt
  rw [hphys, hcomp]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rw [← map_sum, hit]
  show realVec _ = realVec (𝓕⁻ (sspSymbol f) x)
  congr 1
  simp_rw [VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hint]
  rw [freqTrInv_eq_integral]
  simp only [VectorFourier.fourierIntegral]
  rw [← integral_finsetSum _ (fun i _ => integrable_freqTr_integrand
    (f := fun v => VectorFourier.fourierPowSMulRight (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) f v 2
      ![unitVector i, unitVector i])
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) CSpace
      ![unitVector i, unitVector i]).integrable_comp hint) x)]
  congr 1
  funext v
  rw [← Finset.smul_sum]
  congr 1
  simp only [VectorFourier.fourierPowSMulRight_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, neg_apply]
  have hs : ∀ i : Fin 3, (-(2 * (π : ℂ) * Complex.I)) ^ 2 •
      (-((innerSL ℝ) v) (unitVector i) * -((innerSL ℝ) v) (unitVector i)) • f v =
      (-(4 * (π : ℂ) ^ 2) * (((inner ℝ v (unitVector i) * inner ℝ v (unitVector i)) : ℝ) : ℂ)) •
        f v := by
    intro i
    rw [innerSL_apply_apply, neg_mul_neg, ← Complex.coe_smul, smul_smul]
    congr 1
    linear_combination (4 * (π : ℂ) ^ 2 *
      (((inner ℝ v (unitVector i) * inner ℝ v (unitVector i)) : ℝ) : ℂ)) * Complex.I_sq
  rw [Finset.sum_congr rfl (fun i _ => hs i), ← Finset.sum_smul, ← Finset.mul_sum,
    ← Complex.ofReal_sum, sum_inner_unitVector_sq, sspSymbol]
  congr 1
  push_cast
  ring

open Internal in
theorem gradientAt_physScalar {g : Space → ℂ} (hg : Integrable g)
    (hg1 : Integrable (fun ξ => g ξ • freqVec ξ)) (x : Space) :
    gradientAt (physScalar g) x =
      physField (fun ξ => (2 * (π : ℂ) * Complex.I * g ξ) • freqVec ξ) x := by
  have h1 : Integrable (fun v : Space => ‖v‖ * ‖g v‖) := by
    refine hg1.norm.congr (Eventually.of_forall fun ξ => ?_)
    simp only [norm_smul, norm_freqVec, mul_comm]
  have hF : Integrable (fun ξ => (2 * (π : ℂ) * Complex.I * g ξ) • freqVec ξ) :=
    (hg1.smul (2 * (π : ℂ) * Complex.I)).congr
      (Eventually.of_forall fun ξ => by simp only [Pi.smul_apply, smul_smul])
  have hd := hasFDerivAt_freqTrInv hg h1 x
  have hc := Complex.reCLM.hasFDerivAt.comp x hd
  have hfd : ∀ h, fderiv ℝ (physScalar g) x h =
      (𝓕⁻ (fun ξ => (2 * (π : ℂ) * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ)) • g ξ) x).re := by
    intro h
    have hp : physScalar g = Complex.reCLM ∘ 𝓕⁻ g := by
      funext y
      simp [physScalar]
    rw [hp, hc.fderiv, ContinuousLinearMap.comp_apply, freqTrIntegral_smulRight_apply hg h1 x h,
      Complex.reCLM_apply]
  unfold gradientAt
  simp_rw [hfd]
  ext j
  rw [sum_smul_unitVector_apply]
  rw [show ∀ F : Space → CSpace, (physField F x) j = (𝓕⁻ F x j).re from fun F => rfl,
    freqTrInv_coord hF x j]
  refine congrArg Complex.re (congrArg (fun F : Space → ℂ => 𝓕⁻ F x) (funext fun ξ => ?_))
  simp [freqVec, complexifyVec, inner_unitVector]
  ring

open Internal in
theorem divergenceAt_physField {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 1))
    (hdiv : ∀ ξ, ∑ i, ((ξ i : ℝ) : ℂ) * f ξ i = 0) (x : Space) :
    divergenceAt (physField f) x = 0 := by
  have h0 := integrable_of_weight hf
  have h1 : Integrable (fun v : Space => ‖v‖ * ‖f v‖) := by
    simpa using integrable_pow_mul_of_weight hf (le_refl 1)
  have hc : ∀ i : Fin 3, (physField (fun ξ => (2 * (π : ℂ) * Complex.I *
      ((inner ℝ ξ (unitVector i) : ℝ) : ℂ)) • f ξ) x) i =
      (𝓕⁻ (fun ξ => (2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) * f ξ i) x).re := by
    intro i
    rw [show ∀ F : Space → CSpace, (physField F x) i = (𝓕⁻ F x i).re from fun F => rfl,
      freqTrInv_coord (integrable_symbol_smul h0 h1 _) x i]
    simp only [inner_unitVector, PiLp.smul_apply, smul_eq_mul]
  have hi : ∀ i : Fin 3,
      Integrable (fun ξ => (2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) * f ξ i) := by
    intro i
    have := (EuclideanSpace.proj (𝕜 := ℂ) i).integrable_comp
      (integrable_symbol_smul h0 h1 (unitVector i))
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp [inner_unitVector]
  have hz : ∀ ξ : Space, ∑ i : Fin 3, (2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) * f ξ i = 0 := by
    intro ξ
    calc ∑ i : Fin 3, (2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) * f ξ i
        = (2 * (π : ℂ) * Complex.I) * ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * f ξ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hdiv ξ, mul_zero]
  unfold divergenceAt
  simp_rw [fderiv_physField_apply hf x, hc]
  rw [← Complex.re_sum]
  simp_rw [freqTrInv_eq_integral]
  simp only [VectorFourier.fourierIntegral]
  rw [← integral_finsetSum _ (fun i _ => integrable_freqTr_integrand (hi i) x)]
  simp_rw [← Finset.smul_sum, hz, smul_zero, integral_zero, Complex.zero_re]

end Breakdown.SmoothFlow
