import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.PartialDecay

theorem norm_realVec_apply_le (z : CSpace) : ‖realVec z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [realVec, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
  have := Complex.abs_re_le_norm (z i)
  nlinarith [abs_nonneg (z i).re]

theorem l2_norm_sq (f : L2C) : ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  congr 1
  ext ξ
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem norm_sq_space (ξ : Space) : ‖ξ‖ ^ 2 = ∑ k, (ξ k) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp

theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
  exact measure_singleton _

theorem abs_coord_le (ξ : Space) (k : Fin 3) : |ξ k| ≤ ‖ξ‖ := by
  have h : (ξ k) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [norm_sq_space]
    exact Finset.single_le_sum (f := fun i => (ξ i) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have := Real.abs_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

theorem norm_derivSymbol (j : Fin 3) (ξ : Space) : ‖derivSymbol j ξ‖ = |ξ j| / ‖ξ‖ := by
  simp [derivSymbol, Complex.norm_I, Complex.norm_real]

theorem norm_gradSymbol (j : Fin 3) (ξ : Space) : ‖gradSymbol j ξ‖ = |ξ j| / ‖ξ‖ := by
  simp [gradSymbol, Complex.norm_I, Complex.norm_real]

theorem coord_div_le_one (ξ : Space) (k : Fin 3) : |ξ k| / ‖ξ‖ ≤ 1 :=
  div_le_one_of_le₀ (abs_coord_le ξ k) (norm_nonneg _)

theorem cmul_apply (c : ℂ) (z : CSpace) : cmul c z = c • z := rfl

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => by rw [cmul_apply, norm_smul])

theorem continuous_cmul : Continuous cmul := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => ?_)
  have : cmul a - cmul b = cmul (a - b) := by ext z i; simp [cmul_apply, sub_smul]
  rw [dist_eq_norm, dist_eq_norm, this]
  simpa using norm_cmul_le (a - b)

theorem measurable_derivSymbol (j : Fin 3) : Measurable (derivSymbol j) := by
  unfold derivSymbol
  fun_prop

theorem measurable_gradSymbol (j : Fin 3) : Measurable (gradSymbol j) := by
  unfold gradSymbol
  fun_prop

theorem memLp_partialField {f : Space → Space} (hf : IsDecayField f) (j : Fin 3) :
    MemLp (partialField f j) 2 volume := by
  obtain ⟨hs, -, C, hC⟩ := hf
  have hcont : Continuous (partialField f j) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  have hint : Integrable (fun y : Space => C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
    (integrable_one_add_norm (by simp [finrank_euclideanSpace]; norm_num)).const_mul _
  refine hint.mono' (hcont.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have h1 : ‖partialField f j y‖ ≤ C / (1 + ‖y‖) ^ 2 := by
    calc ‖partialField f j y‖ ≤ ‖fderiv ℝ f y‖ * ‖unitVector j‖ := (fderiv ℝ f y).le_opNorm _
      _ = ‖fderiv ℝ f y‖ := by simp [unitVector]
      _ ≤ C / (1 + ‖y‖) ^ 2 := (hC y).2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖partialField f j y‖ ^ 2 ≤ (C / (1 + ‖y‖) ^ 2) ^ 2 := by gcongr
    _ = C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
      rw [Real.rpow_neg hpos.le, div_pow, ← pow_mul, div_eq_mul_inv]
      norm_cast

theorem symbol_identity (a g : Fin 3 → ℂ) (n : ℂ) (hn : n ≠ 0) (hn2 : n ^ 2 = ∑ k, a k ^ 2)
    (hc : ∀ j k, a k * g j = a j * g k) (j : Fin 3) :
    Complex.I * a j / n * ∑ k, (-(Complex.I * a k / n)) * g k = g j := by
  have key : ∑ k, a j * a k * g k = n ^ 2 * g j := by
    rw [hn2, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by linear_combination (-(a k)) * hc j k)
  have hterm : ∀ k, Complex.I * a j / n * (-(Complex.I * a k / n) * g k) = a j * a k * g k / n ^ 2 := by
    intro k
    field_simp
    linear_combination (-(a j * a k * g k)) * Complex.I_sq
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, key,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hn)]

theorem realVec_complexifyVec (z : Space) : realVec (complexifyVec z) = z := by
  ext i
  simp [realVec, complexifyVec]

theorem toPhys_freqTr_complexify (g : L2R) :
    (toPhys (freqTrR (complexify g)) : Space → Space) =ᵐ[volume] g := by
  have e : toPhys (freqTrR (complexify g)) = realPart (complexify g) := by
    show realPart (freqTrL2.symm (freqTrL2 (complexify g))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [e]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec (complexify g),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec g] with x e1 e2
  rw [realPart, e1, complexify, e2, realVec_complexifyVec]

theorem toLpOrZero_ae {f : Space → Space} (hf : MemLp f 2 volume) :
    (toLpOrZero 2 f : Space → Space) =ᵐ[volume] f := by
  unfold toLpOrZero
  rw [dif_pos hf]
  exact hf.coeFn_toLp

theorem symbolOp_ae (h1 : FieldOpRealized) (s : Space → ℂ) (hs : Measurable s)
    (hb : ∀ ξ, ‖s ξ‖ ≤ 1) (f : L2C) :
    (fieldOp id (fun ξ => cmul (s ξ)) f : Space → CSpace) =ᵐ[volume] fun ξ => s ξ • f ξ := by
  have hm : AEStronglyMeasurable (fun ξ => cmul (s ξ)) volume :=
    (continuous_cmul.measurable.comp hs).aestronglyMeasurable
  exact h1 (ContinuousLinearEquiv.refl ℝ Space) _ 1 hm (fun ξ => (norm_cmul_le _).trans (hb ξ)) f

theorem norm_toPhys_le (F : L2C) : ‖toPhys F‖ ≤ ‖F‖ := by
  have hr : ‖realVec‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by simpa using norm_realVec_apply_le z)
  have h2 : ‖freqTrInvR F‖ = ‖F‖ := LinearIsometryEquiv.norm_map freqTrL2.symm F
  calc ‖toPhys F‖ = ‖realVec.compLp (freqTrInvR F)‖ := rfl
    _ ≤ ‖realVec‖ * ‖freqTrInvR F‖ := ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ 1 * ‖freqTrInvR F‖ := by gcongr
    _ = ‖F‖ := by rw [one_mul, h2]

theorem integrable_norm_sq (f : L2C) : Integrable (fun ξ => ‖f ξ‖ ^ 2) volume :=
  (Lp.memLp f).integrable_norm_pow two_ne_zero

theorem sum_norm_derivSymbol_sq_le (ξ : Space) : ∑ j : Fin 3, ‖derivSymbol j ξ‖ ^ 2 ≤ 1 := by
  simp_rw [norm_derivSymbol, div_pow, sq_abs]
  rw [← Finset.sum_div, ← norm_sq_space]
  exact div_self_le_one _

theorem partialNormLe_of (h1 : FieldOpRealized) : PartialNormLe := by
  intro h
  set T : Fin 3 → L2C := fun j => fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (h : L2C) with hT
  have hp : ∀ j, partialX j h = toPhys (T j) := fun j => rfl
  have hae : ∀ j, (T j : Space → CSpace) =ᵐ[volume] fun ξ => derivSymbol j ξ • (h : L2C) ξ :=
    fun j => symbolOp_ae h1 _ (measurable_derivSymbol j)
      (fun ξ => by rw [norm_derivSymbol]; exact coord_div_le_one ξ j) _
  calc ∑ j : Fin 3, ‖partialX j h‖ ^ 2 ≤ ∑ j : Fin 3, ‖T j‖ ^ 2 := by
        gcongr with j
        rw [hp]
        exact norm_toPhys_le _
    _ = ∫ ξ, ∑ j : Fin 3, ‖(T j : Space → CSpace) ξ‖ ^ 2 := by
        rw [integral_finsetSum _ (fun j _ => integrable_norm_sq (T j))]
        exact Finset.sum_congr rfl (fun j _ => l2_norm_sq _)
    _ ≤ ∫ ξ, ‖(h : L2C) ξ‖ ^ 2 := by
        apply integral_mono_ae (integrable_finsetSum _ (fun j _ => integrable_norm_sq (T j)))
          (integrable_norm_sq _)
        filter_upwards [ae_all_iff.2 hae] with ξ hξ
        simp_rw [hξ, norm_smul, mul_pow]
        rw [← Finset.sum_mul]
        exact mul_le_of_le_one_left (sq_nonneg _) (sum_norm_derivSymbol_sq_le ξ)
    _ = ‖(h : L2C)‖ ^ 2 := (l2_norm_sq _).symm
    _ = ‖h‖ ^ 2 := rfl

theorem partialDecay_of (h1 : FieldOpRealized) (h2 : GradCompatible) (h3 : EmbedMem) :
    PartialDecay := by
  intro f hf j
  set G : Fin 3 → L2C := fun k => gradHat f k with hG
  set S : Fin 3 → L2C := fun k => fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (G k) with hSdef
  have hof : ofGrad f = ∑ k, S k := rfl
  have hemb : (embedX f : L2C) = ofGrad f := by
    unfold embedX
    rw [dif_pos (h3 f hf)]
  have hS : ∀ k, (S k : Space → CSpace) =ᵐ[volume] fun ξ => gradSymbol k ξ • (G k : Space → CSpace) ξ :=
    fun k => symbolOp_ae h1 _ (measurable_gradSymbol k)
      (fun ξ => by rw [norm_gradSymbol]; exact coord_div_le_one ξ k) _
  have hsum : (ofGrad f : Space → CSpace) =ᵐ[volume]
      fun ξ => ∑ k, gradSymbol k ξ • (G k : Space → CSpace) ξ := by
    rw [hof, Fin.sum_univ_three]
    filter_upwards [Lp.coeFn_add (S 0 + S 1) (S 2), Lp.coeFn_add (S 0) (S 1), hS 0, hS 1, hS 2]
      with ξ e1 e2 e3 e4 e5
    rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, e4, e5, Fin.sum_univ_three]
  have hT : (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (ofGrad f) : Space → CSpace) =ᵐ[volume]
      (G j : Space → CSpace) := by
    filter_upwards [symbolOp_ae h1 _ (measurable_derivSymbol j)
        (fun ξ => by rw [norm_derivSymbol]; exact coord_div_le_one ξ j) (ofGrad f), hsum, ae_ne_zero,
      ae_all_iff.2 fun j => ae_all_iff.2 fun k => h2 f hf j k] with ξ ea eb hξ hc
    rw [ea, eb]
    ext i
    simp [Finset.sum_apply]
    have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hξ)
    have hn2 : ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ∑ k, ((ξ k : ℝ) : ℂ) ^ 2 := by exact_mod_cast norm_sq_space ξ
    have hc' : ∀ a b : Fin 3, ((ξ b : ℝ) : ℂ) * ((G a : Space → CSpace) ξ) i =
        ((ξ a : ℝ) : ℂ) * ((G b : Space → CSpace) ξ) i := by
      intro a b
      have := congrArg (fun v : CSpace => v i) (hc a b)
      simpa [Complex.real_smul] using this
    unfold derivSymbol gradSymbol
    exact symbol_identity (fun k => ((ξ k : ℝ) : ℂ)) (fun k => ((G k : Space → CSpace) ξ) i) _ hn hn2 hc' j
  have heq : fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (ofGrad f) = G j := Lp.ext hT
  have hp : partialX j (embedX f) = toPhys (G j) := by
    show toPhys (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (embedX f : L2C)) = _
    rw [hemb, heq]
  rw [hp]
  change (toPhys (freqTrR (complexify (toLpOrZero 2 (partialField f j)))) : Space → Space) =ᵐ[volume] _
  exact (toPhys_freqTr_complexify _).trans (toLpOrZero_ae (memLp_partialField hf j))

end Internal.PartialDecay

open Internal.PartialDecay

theorem partialDecayNorm (h1 : FieldOpRealized) (h2 : GradCompatible) (h3 : EmbedMem) :
    PartialDecay ∧ PartialNormLe :=
  ⟨partialDecay_of h1 h2 h3, partialNormLe_of h1⟩

end Breakdown.Freq
