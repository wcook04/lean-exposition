import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.VelocityInjective

scoped instance f65 : Fact ((1 : ℝ≥0∞) ≤ 6 / 5) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]; norm_num⟩

scoped instance hc65 : ENNReal.HolderConjugate (6 : ℝ≥0∞) (6 / 5) := by
  rw [ENNReal.holderConjugate_iff, ENNReal.inv_div (by simp) (by simp), ← one_div,
    ENNReal.div_add_div_same]
  norm_num
  exact ENNReal.div_self (by simp) (by simp)



theorem negSsp_eq (φ : Space → Space) :
    negSsp φ = (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) Space =>
      -∑ i : Fin 3, M ![unitVector i, unitVector i]) ∘ iteratedFDeriv ℝ 2 φ := by
  funext x; rfl

theorem negSsp_continuous (φ : Space → Space) (hφ : IsTestField φ) : Continuous (negSsp φ) := by
  rw [negSsp_eq]
  have h := (contDiff_infty.1 hφ.1 2).continuous_iteratedFDeriv (m := 2) le_rfl
  fun_prop

theorem negSsp_hasCompactSupport (φ : Space → Space) (hφ : IsTestField φ) :
    HasCompactSupport (negSsp φ) := by
  rw [negSsp_eq]
  exact (hφ.2.1.iteratedFDeriv 2).comp_left (by simp)

theorem partialField_continuous (ψ : Space → Space) (hψ : IsTestField ψ) (l : Fin 3) :
    Continuous (partialField ψ l) := by
  have h := hψ.1.continuous_fderiv (by simp)
  unfold partialField
  fun_prop

theorem partialField_hasCompactSupport (ψ : Space → Space) (hψ : IsTestField ψ) (l : Fin 3) :
    HasCompactSupport (partialField ψ l) := by
  have h : partialField ψ l = (fun M : Space →L[ℝ] Space => M (unitVector l)) ∘ fderiv ℝ ψ := by
    funext x; rfl
  rw [h]
  exact (hψ.2.1.fderiv (𝕜 := ℝ)).comp_left (by simp)

theorem isDecayField_of_test (ψ : Space → Space) (hψ : IsTestField ψ) : IsDecayField ψ := by
  refine ⟨hψ.1, hψ.2.2, ?_⟩
  obtain ⟨M1, hM1⟩ := hψ.1.continuous.bounded_above_of_compact_support hψ.2.1
  obtain ⟨M2, hM2⟩ := (hψ.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hψ.2.1.fderiv (𝕜 := ℝ))
  obtain ⟨R, hR⟩ := hψ.2.1.isCompact.isBounded.subset_closedBall 0
  have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hM2' : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0)
  set R' := max R 0
  refine ⟨(M1 + M2) * (1 + R') ^ 2, fun y => ?_⟩
  have hy0 : 0 < 1 + ‖y‖ := by positivity
  by_cases hy : y ∈ tsupport ψ
  · have hyR : ‖y‖ ≤ R' := by
      have := hR hy
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have hR0 : 0 ≤ R' := le_max_right _ _
    have h1 : 1 + ‖y‖ ≤ (1 + R') ^ 2 := by nlinarith
    have h2 : (1 + ‖y‖) ^ 2 ≤ (1 + R') ^ 2 := by
      apply pow_le_pow_left₀ hy0.le; linarith
    constructor
    · rw [le_div_iff₀ hy0]
      calc ‖ψ y‖ * (1 + ‖y‖) ≤ (M1 + M2) * (1 + R') ^ 2 := by
            apply mul_le_mul (by linarith [hM1 y]) h1 hy0.le (by linarith)
        _ = _ := rfl
    · rw [le_div_iff₀ (by positivity)]
      apply mul_le_mul (by linarith [hM2 y]) h2 (by positivity) (by linarith)
  · have e1 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have e2 : fderiv ℝ ψ y = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hy
    rw [e1, e2, norm_zero, norm_zero]
    constructor <;> positivity

theorem hasCompactSupport_inner_left {f g : Space → Space} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => inner ℝ (f x) (g x)) :=
  hf.mono' (fun x hx => subset_tsupport f (by intro h; apply hx; simp [h]))

theorem second_partial_eq (φ : Space → Space) (hφ : IsTestField φ) (e : Space) (x : Space) :
    fderiv ℝ (fun y => fderiv ℝ φ y e) x e = iteratedFDeriv ℝ 2 φ x ![e, e] := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    ((contDiff_infty.1 hφ.1 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply (hd x) (differentiableAt_const e)]
  simp

theorem ibp_one (ψ φ : Space → Space) (hψ : IsTestField ψ) (hφ : IsTestField φ) (l : Fin 3) :
    ∫ x, inner ℝ (partialField ψ l x) (partialField φ l x) =
      -∫ x, inner ℝ (ψ x) (iteratedFDeriv ℝ 2 φ x ![unitVector l, unitVector l]) := by
  have hD : Continuous (fun x => iteratedFDeriv ℝ 2 φ x ![unitVector l, unitVector l]) := by
    have h := (contDiff_infty.1 hφ.1 2).continuous_iteratedFDeriv (m := 2) le_rfl
    fun_prop
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    ((contDiff_infty.1 hφ.1 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e : ∀ x, fderiv ℝ (partialField φ l) x (unitVector l) =
      iteratedFDeriv ℝ 2 φ x ![unitVector l, unitVector l] := fun x => second_partial_eq φ hφ _ x
  have i1 : Integrable (fun x => inner ℝ (partialField ψ l x) (partialField φ l x)) volume :=
    ((partialField_continuous ψ hψ l).inner (partialField_continuous φ hφ l)).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left (partialField_hasCompactSupport ψ hψ l))
  have i2 : Integrable (fun x => inner ℝ (ψ x) (fderiv ℝ (partialField φ l) x (unitVector l))) volume := by
    simp only [e]
    exact (hψ.1.continuous.inner hD).integrable_of_hasCompactSupport (hasCompactSupport_inner_left hψ.2.1)
  have i3 : Integrable (fun x => inner ℝ (ψ x) (partialField φ l x)) volume :=
    (hψ.1.continuous.inner (partialField_continuous φ hφ l)).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left hψ.2.1)
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (f := ψ) (g := partialField φ l) (v := unitVector l) (B := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ))
    i1 i2 i3 (fun x _ => hψ.1.differentiable (by simp) x)
    (fun x _ => (hd x).clm_apply (differentiableAt_const _))
  simp only [e] at key
  have key2 : ∫ x, inner ℝ (ψ x) (iteratedFDeriv ℝ 2 φ x ![unitVector l, unitVector l]) =
      -∫ x, inner ℝ (partialField ψ l x) (partialField φ l x) := key
  rw [key2, neg_neg]

theorem ibp_test (ψ φ : Space → Space) (hψ : IsTestField ψ) (hφ : IsTestField φ) :
    ∫ x, ∑ l : Fin 3, inner ℝ (partialField ψ l x) (partialField φ l x) =
      ∫ x, inner ℝ (ψ x) (negSsp φ x) := by
  have hD : ∀ l : Fin 3, Continuous (fun x => iteratedFDeriv ℝ 2 φ x ![unitVector l, unitVector l]) := by
    intro l
    have h := (contDiff_infty.1 hφ.1 2).continuous_iteratedFDeriv (m := 2) le_rfl
    fun_prop
  have i1 : ∀ l ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x => inner ℝ (partialField ψ l x) (partialField φ l x)) volume := fun l _ =>
    ((partialField_continuous ψ hψ l).inner (partialField_continuous φ hφ l)).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left (partialField_hasCompactSupport ψ hψ l))
  have i2 : ∀ l ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x => inner ℝ (ψ x) (iteratedFDeriv ℝ 2 φ x ![unitVector l, unitVector l])) volume :=
    fun l _ => (hψ.1.continuous.inner (hD l)).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left hψ.2.1)
  rw [integral_finsetSum _ i1]
  simp only [ibp_one ψ φ hψ hφ]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ i2, ← integral_neg]
  congr 1
  funext x
  simp only [negSsp, sumSecondPartialsAt, inner_neg_right, inner_sum]



theorem cmul_eq : cmul = fun c : ℂ => c • ((ContinuousLinearMap.id ℂ CSpace).restrictScalars ℝ) := by
  funext c; ext z; simp [cmul]

theorem cmul_continuous : Continuous cmul := by
  rw [cmul_eq]; exact continuous_id.smul continuous_const

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z; simp [cmul, norm_smul]

theorem norm_gradSymbol_le (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  unfold gradSymbol
  rw [norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_norm]
  exact div_le_one_of_le₀ (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ k) (norm_nonneg _)

theorem gradSymbol_measurable (k : Fin 3) : Measurable (gradSymbol k) := by
  unfold gradSymbol; fun_prop

theorem realized_grad (h5 : FieldOpRealized) (k : Fin 3) :
    IsRealizedBy (fieldOp id (fun ξ => cmul (gradSymbol k ξ))) id (fun ξ => cmul (gradSymbol k ξ)) :=
  h5 (ContinuousLinearEquiv.refl ℝ Space) _ 1
    (cmul_continuous.measurable.comp (gradSymbol_measurable k)).aestronglyMeasurable
    (fun ξ => (norm_cmul_le _).trans (norm_gradSymbol_le k ξ))

theorem ofGrad_ae (h5 : FieldOpRealized) (ψ : Space → Space) :
    (ofGrad ψ : Space → CSpace) =ᵐ[volume] fun ξ => ∑ k : Fin 3, gradSymbol k ξ • (gradHat ψ k : Space → CSpace) ξ := by
  unfold ofGrad
  rw [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (_ + _ : L2C) _, Lp.coeFn_add (_ : L2C) _,
    realized_grad h5 0 (gradHat ψ 0), realized_grad h5 1 (gradHat ψ 1), realized_grad h5 2 (gradHat ψ 2)] with ξ a1 a2 r0 r1 r2
  rw [a1, Pi.add_apply, a2, Pi.add_apply]
  simp only [Fin.sum_univ_three]
  unfold gradHat at *
  rw [r0, r1, r2]
  simp [cmul]


theorem gradSymbol_pair (ξ : Space) (k l : Fin 3) :
    starRingEnd ℂ (gradSymbol k ξ) * gradSymbol l ξ =
      ((ξ k : ℝ) : ℂ) * ((ξ l : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
  simp only [gradSymbol, map_neg, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem inner_grad_sum (ξ : Space) (hξ : ξ ≠ 0) (G H : Fin 3 → CSpace)
    (hG : ∀ j k : Fin 3, (ξ k : ℝ) • G j = (ξ j : ℝ) • G k) :
    inner ℂ (∑ k, gradSymbol k ξ • G k) (∑ l, gradSymbol l ξ • H l) = ∑ l, inner ℂ (G l) (H l) := by
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hξ
  have key : ∀ k l, starRingEnd ℂ (gradSymbol k ξ) * gradSymbol l ξ * inner ℂ (G k) (H l) =
      ((ξ k : ℝ) : ℂ) ^ 2 / ((‖ξ‖ : ℝ) : ℂ) ^ 2 * inner ℂ (G l) (H l) := by
    intro k l
    have e := congrArg (fun v => inner ℂ v (H l)) (hG k l)
    simp only [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal] at e
    rw [gradSymbol_pair]
    calc ((ξ k : ℝ) : ℂ) * ((ξ l : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) ^ 2 * inner ℂ (G k) (H l)
        = ((ξ k : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) ^ 2 * (((ξ l : ℝ) : ℂ) * inner ℂ (G k) (H l)) := by ring
      _ = ((ξ k : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) ^ 2 * (((ξ k : ℝ) : ℂ) * inner ℂ (G l) (H l)) := by
          rw [← e]
      _ = _ := by ring
  have hsum : ∑ k : Fin 3, ((ξ k : ℝ) : ℂ) ^ 2 = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
    have h := EuclideanSpace.norm_sq_eq ξ
    rw [← Complex.ofReal_pow, h]
    simp only [Real.norm_eq_abs, sq_abs]
    push_cast
    rfl
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hk : ∀ k, gradSymbol l ξ * (starRingEnd ℂ (gradSymbol k ξ) * inner ℂ (G k) (H l)) =
      ((ξ k : ℝ) : ℂ) ^ 2 / ((‖ξ‖ : ℝ) : ℂ) ^ 2 * inner ℂ (G l) (H l) := fun k => by
    rw [← key k l]; ring
  rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.sum_mul, ← Finset.sum_div, hsum, div_self (pow_ne_zero 2 hn), one_mul]

theorem complexifyVec_inner (u v : Space) :
    RCLike.re (inner ℂ (complexifyVec u) (complexifyVec v)) = inner ℝ u v := by
  simp [complexifyVec, PiLp.inner_apply]

theorem l2c_real_inner (f g : L2C) : inner ℝ f g = RCLike.re (inner ℂ f g) := by
  rw [L2.inner_def, L2.inner_def (𝕜 := ℂ), ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => real_inner_eq_re_inner ℂ _ _)

theorem complexify_inner (a b : L2R) : inner ℝ (complexify a) (complexify b) = inner ℝ a b := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec a,
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec b] with x ha hb
  unfold complexify
  rw [ha, hb]
  exact (real_inner_eq_re_inner ℂ _ _).trans (complexifyVec_inner _ _)

theorem freqTrR_inner (f g : L2C) : inner ℝ (freqTrR f) (freqTrR g) = inner ℝ f g := by
  rw [l2c_real_inner, l2c_real_inner]
  exact congrArg _ (freqTrL2.inner_map_map f g)

theorem inner_ofGrad (h5 : FieldOpRealized) (h6 : GradCompatible) (ψ φ : Space → Space)
    (hψ : IsDecayField ψ) (hmψ : ∀ l, MemLp (partialField ψ l) 2 volume)
    (hmφ : ∀ l, MemLp (partialField φ l) 2 volume) :
    inner ℝ (ofGrad ψ) (ofGrad φ) = ∑ l : Fin 3, ∫ x, inner ℝ (partialField ψ l x) (partialField φ l x) := by
  rw [l2c_real_inner, L2.inner_def]
  have hne : ∀ᵐ ξ ∂(volume : Measure Space), ξ ∉ ({0} : Set Space) :=
    (Set.countable_singleton (0 : Space)).ae_notMem volume
  have hgc : ∀ᵐ ξ ∂(volume : Measure Space), ∀ j k : Fin 3,
      (ξ k : ℝ) • (gradHat ψ j : Space → CSpace) ξ = (ξ j : ℝ) • (gradHat ψ k : Space → CSpace) ξ := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro k; exact h6 ψ hψ j k
  have hpt : (fun ξ => inner ℂ ((ofGrad ψ : Space → CSpace) ξ) ((ofGrad φ : Space → CSpace) ξ)) =ᵐ[volume]
      fun ξ => ∑ l : Fin 3, inner ℂ ((gradHat ψ l : Space → CSpace) ξ) ((gradHat φ l : Space → CSpace) ξ) := by
    filter_upwards [ofGrad_ae h5 ψ, ofGrad_ae h5 φ, hne, hgc] with ξ e1 e2 e3 e4
    rw [e1, e2]
    exact inner_grad_sum ξ (by simpa using e3) _ _ (fun j k => e4 j k)
  rw [integral_congr_ae hpt, integral_finsetSum _ (fun l _ => L2.integrable_inner _ _), map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← L2.inner_def, ← l2c_real_inner]
  unfold gradHat
  rw [freqTrR_inner, complexify_inner, L2.inner_def]
  apply integral_congr_ae
  have e1 : ((toLpOrZero 2 (partialField ψ l) : L2R) : Space → Space) =ᵐ[volume] partialField ψ l := by
    unfold toLpOrZero; rw [dif_pos (hmψ l)]; exact (hmψ l).coeFn_toLp
  have e2 : ((toLpOrZero 2 (partialField φ l) : L2R) : Space → Space) =ᵐ[volume] partialField φ l := by
    unfold toLpOrZero; rw [dif_pos (hmφ l)]; exact (hmφ l).coeFn_toLp
  filter_upwards [e1, e2] with x a b
  rw [a, b]

theorem pairing_test (h4 : EmbedMem) (h5 : FieldOpRealized) (h6 : GradCompatible)
    (ψ φ : Space → Space) (hψ : IsTestField ψ) (hφ : IsTestField φ) :
    inner ℝ (embedX ψ) (embedX φ) = ∫ x, inner ℝ (ψ x) (negSsp φ x) := by
  have dψ := isDecayField_of_test ψ hψ
  have dφ := isDecayField_of_test φ hφ
  have mψ : ∀ l, MemLp (partialField ψ l) 2 volume := fun l =>
    (partialField_continuous ψ hψ l).memLp_of_hasCompactSupport (partialField_hasCompactSupport ψ hψ l)
  have mφ : ∀ l, MemLp (partialField φ l) 2 volume := fun l =>
    (partialField_continuous φ hφ l).memLp_of_hasCompactSupport (partialField_hasCompactSupport φ hφ l)
  have iψφ : ∀ l, Integrable (fun x => inner ℝ (partialField ψ l x) (partialField φ l x)) volume := fun l =>
    ((partialField_continuous ψ hψ l).inner (partialField_continuous φ hφ l)).integrable_of_hasCompactSupport
      ((partialField_hasCompactSupport ψ hψ l).mono (by
        intro x hx; simp only [Function.mem_support] at hx ⊢; intro h; apply hx; rw [h, inner_zero_left]))
  have e : inner ℝ (embedX ψ) (embedX φ) = inner ℝ (ofGrad ψ) (ofGrad φ) := by
    unfold embedX
    rw [dif_pos (h4 ψ dψ), dif_pos (h4 φ dφ)]
    rfl
  rw [e, inner_ofGrad h5 h6 ψ φ dψ mψ mφ, ← integral_finsetSum _ (fun l _ => iψφ l), ibp_test ψ φ hψ hφ]

theorem toLp6_test (ψ : Space → Space) (hψ : IsTestField ψ) :
    ((toLpOrZero 6 ψ : L6R) : Space → Space) =ᵐ[volume] ψ := by
  have hm : MemLp ψ 6 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  unfold toLpOrZero; rw [dif_pos hm]; exact hm.coeFn_toLp

end Internal.VelocityInjective

open Internal.VelocityInjective in
theorem velocityInjective (h1 : VelocityExists) (h2 : TestDense) (h3 : TestSpanSpec) (h4 : EmbedMem)
    (h5 : FieldOpRealized) (h6 : GradCompatible) (_h7 : EmbedLinear) :
    VelocityInjective := by
  intro x hx
  have hspec : VelocitySpec velocity := by
    unfold velocity VelocityExists at *; rw [dif_pos h1]; exact h1.choose_spec
  have key : ∀ φ, IsTestField φ → inner ℝ x (embedX φ) = 0 := by
    intro φ hφ
    have hG : MemLp (negSsp φ) (6 / 5) volume :=
      (negSsp_continuous φ hφ).memLp_of_hasCompactSupport (negSsp_hasCompactSupport φ hφ)
    let P := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing (volume : Measure Space) 6 (6 / 5)
    have heq : (fun y : X => inner ℝ y (embedX φ)) = fun y => P (velocity y) (hG.toLp _) := by
      apply Continuous.ext_on h2 (by fun_prop) ((P.flip (hG.toLp _)).continuous.comp velocity.continuous)
      intro y hy
      obtain ⟨ψ, hψ, rfl⟩ := h3 y hy
      show inner ℝ (embedX ψ) (embedX φ) = P (velocity (embedX ψ)) (hG.toLp _)
      rw [pairing_test h4 h5 h6 ψ φ hψ hφ]
      simp only [P]
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [(hspec ψ hψ) ▸ toLp6_test ψ hψ, hG.coeFn_toLp] with z hz1 hz2
      rw [hz1, hz2]; rfl
    have e : inner ℝ x (embedX φ) = P (velocity x) (hG.toLp _) := congrFun heq x
    have h0 : velocity x = 0 := Lp.eq_zero_iff_ae_eq_zero.2 hx
    rw [e, h0]; simp
  have hall : (fun y : X => inner ℝ x y) = fun _ => (0 : ℝ) := by
    apply Continuous.ext_on h2 (by fun_prop) continuous_const
    intro y hy
    obtain ⟨φ, hφ, rfl⟩ := h3 y hy
    exact key φ hφ
  have := congrFun hall x
  simpa using this

end Breakdown.Freq
