import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.BilinTestFormula

theorem toLpOrZero_ae {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : Space → F}
    (hf : MemLp f p volume) : (toLpOrZero p f : Space → F) =ᵐ[volume] f := by
  unfold toLpOrZero
  rw [dif_pos hf]
  exact hf.coeFn_toLp

theorem test_memLp {φ : Space → Space} (hφ : IsTestField φ) (p : ℝ≥0∞) : MemLp φ p volume :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1

theorem velocity_spec (h2 : VelocityExists) : VelocitySpec velocity := by
  have h : ∃ V, VelocitySpec V := h2
  unfold velocity
  rw [dif_pos h]
  exact h.choose_spec

theorem velocity_test (h2 : VelocityExists) {φ : Space → Space} (hφ : IsTestField φ) :
    (velocity (embedX φ) : Space → Space) =ᵐ[volume] φ := by
  rw [velocity_spec h2 φ hφ]
  exact toLpOrZero_ae (test_memLp hφ 6)

theorem bilinX_spec (h1 : BilinExists) {τ : ℝ} (hτ : 0 < τ) : BilinSpec τ (bilinX τ) := by
  have h : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, h1 τ hτ⟩
  unfold bilinX
  rw [dif_pos h]
  exact h.2.choose_spec

theorem fieldOp_id_ae (h3 : FieldOpRealized) (F : Space → CSpace →L[ℝ] CSpace) (C : ℝ)
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) (f : L2C) :
    (fieldOp id F f : Space → CSpace) =ᵐ[volume] fun ξ => F ξ (f ξ) := by
  have h := h3 (ContinuousLinearEquiv.refl ℝ Space) F C hF hC f
  simpa using h


theorem cmul_apply (c : ℂ) (z : CSpace) : cmul c z = c • z := rfl

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => by rw [cmul_apply, norm_smul])

theorem continuous_cmul : Continuous cmul := by
  have : cmul = fun c : ℂ => c • ContinuousLinearMap.id ℝ CSpace := by
    funext c
    ext1 z
    simp [cmul_apply]
  rw [this]
  exact continuous_id.smul continuous_const

theorem symbol_ae (h3 : FieldOpRealized) (s : Space → ℂ) (hs : Measurable s)
    (hb : ∀ ξ, ‖s ξ‖ ≤ 1) (f : L2C) :
    (fieldOp id (fun ξ => cmul (s ξ)) f : Space → CSpace) =ᵐ[volume] fun ξ => s ξ • f ξ := by
  have h := fieldOp_id_ae h3 (fun ξ => cmul (s ξ)) 1
    (continuous_cmul.comp_aestronglyMeasurable hs.aestronglyMeasurable)
    (fun ξ => (norm_cmul_le _).trans (hb ξ)) f
  simpa [cmul_apply] using h

theorem norm_derivSymbol_le (j : Fin 3) (ξ : Space) : ‖derivSymbol j ξ‖ ≤ 1 := by
  unfold derivSymbol
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, norm_norm]
  exact div_le_one_of_le₀ (PiLp.norm_apply_le ξ j) (norm_nonneg _)

theorem measurable_derivSymbol (j : Fin 3) : Measurable (derivSymbol j) := by
  unfold derivSymbol
  fun_prop

theorem gradSymbol_eq (k : Fin 3) (ξ : Space) : gradSymbol k ξ = -derivSymbol k ξ := rfl

theorem ofGrad_zero : ofGrad (0 : Space → Space) = 0 := by
  have h0 : ∀ k, partialField (0 : Space → Space) k = 0 := by
    intro k
    funext x
    simp [partialField]
  have h1 : toLpOrZero 2 (0 : Space → Space) = 0 := by
    unfold toLpOrZero
    rw [dif_pos MemLp.zero]
    exact MemLp.toLp_zero _
  simp [ofGrad, h0, h1]

theorem ofGrad_mem_of_test (h2 : VelocityExists) {φ : Space → Space} (hφ : IsTestField φ) :
    ofGrad φ ∈ Sig := by
  by_contra hm
  have he : embedX φ = 0 := by
    unfold embedX
    rw [dif_neg hm]
  have hv := velocity_test h2 hφ
  rw [he, map_zero] at hv
  have hz : (fun _ => 0 : Space → Space) = φ := by
    rw [← Continuous.ae_eq_iff_eq volume continuous_const hφ.1.continuous]
    exact (Lp.coeFn_zero _ _ _).symm.trans hv
  apply hm
  rw [← hz]
  exact ofGrad_zero ▸ zero_mem _

theorem partialField_memLp {φ : Space → Space} (hφ : IsTestField φ) (k : Fin 3) (p : ℝ≥0∞) :
    MemLp (partialField φ k) p volume := by
  have hc : Continuous (partialField φ k) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (partialField φ k) :=
    (hφ.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector k)) (by simp)
  exact hc.memLp_of_hasCompactSupport hs

theorem realVec_complexifyVec (z : Space) : realVec (complexifyVec z) = z := by
  ext i
  simp [realVec, complexifyVec]

open SchwartzMap FourierTransform LineDeriv in
theorem gradHat_ae {φ : Space → Space} (hφ : IsTestField φ) (S : 𝓢(Space, CSpace))
    (hS : ∀ x, S x = complexifyVec (φ x)) (k : Fin 3) :
    (freqTrR (complexify (toLpOrZero 2 (partialField φ k))) : Space → CSpace) =ᵐ[volume]
      fun ξ => (2 * π * Complex.I) • ((ξ k : ℝ) • (𝓕 S) ξ) := by
  have hSf : (S : Space → CSpace) = fun x => complexifyVec (φ x) := funext hS
  have e1 : complexify (toLpOrZero 2 (partialField φ k)) = (∂_{unitVector k} S).toLp 2 := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec
        (toLpOrZero 2 (partialField φ k)), toLpOrZero_ae (partialField_memLp hφ k 2),
        SchwartzMap.coeFn_toLp (∂_{unitVector k} S) 2 volume] with x h1 h2 h3
    rw [complexify, h1, h2, h3, lineDerivOp_apply_eq_fderiv, hSf]
    have hd : HasFDerivAt (fun x => complexifyVec (φ x)) (complexifyVec.comp (fderiv ℝ φ x)) x :=
      complexifyVec.hasFDerivAt.comp x ((hφ.1.differentiable (by simp) x).hasFDerivAt)
    rw [hd.fderiv]
    rfl
  have e2 : freqTrR ((∂_{unitVector k} S).toLp 2) = (𝓕 (∂_{unitVector k} S)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq _
  rw [e1, e2]
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (∂_{unitVector k} S)) 2 volume] with ξ h
  rw [h, fourier_lineDerivOp_eq]
  have hg : (fun x : Space => inner ℝ x (unitVector k)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (unitVector k)).hasTemperateGrowth
  rw [smul_apply, smulLeftCLM_apply_apply hg]
  simp [unitVector, EuclideanSpace.inner_single_right]

open SchwartzMap FourierTransform in
theorem partial_test (h2 : VelocityExists) (h3 : FieldOpRealized) {φ : Space → Space}
    (hφ : IsTestField φ) (j : Fin 3) :
    (partialX j (embedX φ) : Space → Space) =ᵐ[volume] partialField φ j := by
  have hm := ofGrad_mem_of_test h2 hφ
  have he : (embedX φ : L2C) = ofGrad φ := by
    unfold embedX
    rw [dif_pos hm]
  let S : 𝓢(Space, CSpace) :=
    (hφ.2.1.comp_left (g := complexifyVec) (map_zero _)).toSchwartzMap
      (complexifyVec.contDiff.comp hφ.1)
  have hS : ∀ x, S x = complexifyVec (φ x) := fun x => rfl
  set y : Fin 3 → L2C := fun k => freqTrR (complexify (toLpOrZero 2 (partialField φ k))) with hy
  set G : Fin 3 → L2C := fun k => fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (y k) with hG
  have hsum : ofGrad φ = G 0 + G 1 + G 2 := by
    simp only [ofGrad, Fin.sum_univ_three, hG, hy]
  have hGk : ∀ k, (G k : Space → CSpace) =ᵐ[volume] fun ξ => gradSymbol k ξ • (y k) ξ := fun k =>
    symbol_ae h3 (gradSymbol k) (measurable_derivSymbol k).neg
      (fun ξ => by rw [gradSymbol_eq, norm_neg]; exact norm_derivSymbol_le k ξ) (y k)
  have key : fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (ofGrad φ) = y j := by
    apply Lp.ext
    rw [hsum]
    filter_upwards [symbol_ae h3 (derivSymbol j) (measurable_derivSymbol j) (norm_derivSymbol_le j)
        (G 0 + G 1 + G 2), Lp.coeFn_add (G 0 + G 1) (G 2), Lp.coeFn_add (G 0) (G 1),
        hGk 0, hGk 1, hGk 2, gradHat_ae hφ S hS 0, gradHat_ae hφ S hS 1, gradHat_ae hφ S hS 2,
        gradHat_ae hφ S hS j, Measure.ae_ne volume 0] with ξ hD ha1 ha2 hg0 hg1 hg2 hy0 hy1 hy2 hyj hξ
    rw [hD, ha1, Pi.add_apply, ha2, Pi.add_apply, hg0, hg1, hg2]
    simp only [hy]
    rw [hy0, hy1, hy2, hyj]
    simp only [← Complex.coe_smul, smul_smul, ← add_smul]
    congr 1
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hr : ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2 := by
      have : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      exact_mod_cast this
    have hr0 : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
    unfold derivSymbol gradSymbol
    trans 2 * (π : ℂ) * Complex.I * ((ξ j : ℝ) : ℂ) * (-(Complex.I * Complex.I)) *
      ((((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2) / ((‖ξ‖ : ℝ) : ℂ) ^ 2)
    · ring
    · rw [hI, ← hr, div_self (pow_ne_zero 2 hr0)]
      ring
  have hpx : partialX j (embedX φ) = realPart (complexify (toLpOrZero 2 (partialField φ j))) := by
    simp only [partialX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, he, key, hy]
    simp [toPhys, freqTrInvR, freqTrR]
  rw [hpx]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec
      (complexify (toLpOrZero 2 (partialField φ j))),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec
      (toLpOrZero 2 (partialField φ j)), toLpOrZero_ae (partialField_memLp hφ j 2)] with x h1 h2 h3
  rw [realPart, h1, complexify, h2, h3, realVec_complexifyVec]



private theorem inner_complexifyVec (a : Space) (b : CSpace) :
    inner ℝ (complexifyVec a) b = inner ℝ a (realVec b) := by
  simp [complexifyVec, realVec, PiLp.inner_apply, Complex.inner]

private theorem inner_complexify (g : L2R) (z : L2C) :
    inner ℝ (complexify g) z = inner ℝ g (realPart z) := by
  have hx : (complexify g : Space → CSpace) =ᵐ[volume] fun a => complexifyVec (g a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hy : (realPart z : Space → Space) =ᵐ[volume] fun a => realVec (z a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx, hy] with x hx hy
  rw [hx, hy, inner_complexifyVec]

private def freqTrRealIsometry : L2C ≃ₗᵢ[ℝ] L2C :=
  { freqTrL2.toLinearEquiv.restrictScalars ℝ with norm_map' := freqTrL2.norm_map }

private theorem inner_freqTrR (a b : L2C) :
    inner ℝ (freqTrR a) b = inner ℝ a (freqTrInvR b) :=
  freqTrRealIsometry.inner_map_eq_flip a b

private theorem phiFactor_nonneg (τ : ℝ) (ξ : Space) : 0 ≤ phiFactor τ ξ := by
  unfold phiFactor; positivity

private theorem norm_phiFactor_smul_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    ‖phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 + 1 / τ := by
  refine (norm_smul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
  rw [mul_one, Real.norm_eq_abs, abs_of_nonneg (phiFactor_nonneg τ ξ)]
  unfold phiFactor
  have ha : 0 ≤ 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 := by positivity
  have he := Real.add_one_le_exp (4 * π ^ 2 * τ * ‖ξ‖ ^ 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have hy : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  have h1 : (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) =
      4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1 + (2 * π * ‖ξ‖) ^ 2 + 1 / τ := by
    field_simp
    ring
  have h2 : 2 * π * ‖ξ‖ ≤ (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) := by
    rw [h1]
    have : 0 ≤ 1 / τ := by positivity
    nlinarith [sq_nonneg (2 * π * ‖ξ‖ - 1)]
  calc 2 * π * ‖ξ‖ ≤ (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) := h2
    _ ≤ (1 + 1 / τ) * Real.exp (4 * π ^ 2 * τ * ‖ξ‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left he; positivity

theorem heatDivFree_inner (h3 : FieldOpRealized) {τ : ℝ} (hτ : 0 < τ) (g : L2R) (ψ : X) :
    inner ℝ (heatDivFree τ g) ψ = inner ℝ g (phiX τ ψ) := by
  set M := fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) with hMdef
  have hM : ∀ f : L2C, (M f : Space → CSpace) =ᵐ[volume] fun ξ => phiFactor τ ξ • f ξ := by
    intro f
    have hc : Continuous (fun ξ : Space => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) := by
      unfold phiFactor; fun_prop
    have := fieldOp_id_ae h3 _ (1 + 1 / τ) hc.aestronglyMeasurable (norm_phiFactor_smul_le hτ) f
    simpa using this
  have hsa : ∀ a b : L2C, inner ℝ (M a) b = inner ℝ a (M b) := by
    intro a b
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hM a, hM b] with x ha hb
    rw [ha, hb, real_inner_smul_left, real_inner_smul_right]
  have hproj : ∀ w : L2C, inner ℝ (projX w) ψ = inner ℝ w (ψ : L2C) := fun w =>
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right ψ w
  show inner ℝ (projX (M (freqTrR (complexify g)))) ψ = inner ℝ g (realPart (freqTrInvR (M ψ)))
  rw [hproj, hsa, inner_freqTrR, inner_complexify]


private theorem lpProd_six_three : ENNReal.HolderTriple 6 3 2 := by
  constructor
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

private theorem integrable_inner_of_memLp {f g : Space → Space} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : Integrable (fun x => inner ℝ (f x) (g x)) volume := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  refine h.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

private theorem coord_memLp {f : Space → Space} {p : ℝ≥0∞} (hf : MemLp f p volume) (j : Fin 3) :
    MemLp (fun x => f x j) p volume :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp_memLp' hf

theorem trilinear_sum (h2 : VelocityExists) (h3 : FieldOpRealized) {φ : Space → Space}
    (hφ : IsTestField φ) (v : X) (w : L2R) :
    trilinear (embedX φ) v (w : Space → Space) + trilinear v (embedX φ) (w : Space → Space) =
      inner ℝ (advectTest φ v) w := by
  have hT1 : ∀ j : Fin 3, MemLp (fun x => φ x j • (partialX j v : Space → Space) x) 2 volume :=
    fun j => (Lp.memLp (partialX j v)).smul (coord_memLp (test_memLp hφ ⊤) j)
  have hT2 : ∀ j : Fin 3, MemLp (fun x => (velocity v : Space → Space) x j • partialField φ j x)
      2 volume := by
    intro j
    have := lpProd_six_three
    exact (partialField_memLp hφ j 3).smul (coord_memLp (Lp.memLp (velocity v)) j)
  have hA : MemLp (fun x => ∑ j : Fin 3, (φ x j • (partialX j v : Space → Space) x +
      (velocity v : Space → Space) x j • partialField φ j x)) 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => (hT1 j).add (hT2 j))
  have hadv := toLpOrZero_ae hA
  have hw : MemLp (w : Space → Space) 2 volume := Lp.memLp w
  have e1 : trilinear (embedX φ) v (w : Space → Space) =
      ∫ x, ∑ j : Fin 3, inner ℝ (φ x j • (partialX j v : Space → Space) x) (w x) := by
    unfold trilinear
    apply integral_congr_ae
    filter_upwards [velocity_test h2 hφ] with x hx
    simp only [hx, real_inner_smul_left]
  have e2 : trilinear v (embedX φ) (w : Space → Space) =
      ∫ x, ∑ j : Fin 3, inner ℝ ((velocity v : Space → Space) x j • partialField φ j x) (w x) := by
    unfold trilinear
    apply integral_congr_ae
    filter_upwards [ae_all_iff.2 (fun j => partial_test h2 h3 hφ j)] with x hx
    simp only [hx, real_inner_smul_left]
  rw [e1, e2, ← integral_add (integrable_finsetSum _ (fun j _ => integrable_inner_of_memLp (hT1 j) hw))
    (integrable_finsetSum _ (fun j _ => integrable_inner_of_memLp (hT2 j) hw)),
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hadv] with x hx
  unfold advectTest
  rw [hx, sum_inner, ← Finset.sum_add_distrib]
  simp only [inner_add_left]

end Internal.BilinTestFormula

open Internal.BilinTestFormula in
theorem bilinTestFormula (h1 : BilinExists) (h2 : VelocityExists) (h3 : FieldOpRealized)
    (_h4 : TrilinearBound) (_h5 : PartialNormLe) : BilinTestFormula := by
  intro φ hφ τ hτ v
  apply ext_inner_right ℝ
  intro ψ
  rw [bilinX_spec h1 hτ, real_inner_smul_left, heatDivFree_inner h3 hτ, bilinForm,
    trilinear_sum h2 h3 hφ v]

end Breakdown.Freq
