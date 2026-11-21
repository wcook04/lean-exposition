import Breakdown.FreqTr.StatementsExport

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.Freq

namespace Internal.H1Consistency

open SchwartzMap LineDeriv

theorem toLpOrZero_ae {f : Space → Space} (hf : MemLp f 2 volume) :
    (toLpOrZero 2 f : Space → Space) =ᵐ[volume] f := by
  rw [toLpOrZero, dif_pos hf]
  exact hf.coeFn_toLp

theorem toPhys_freqTr_complexify (g : L2R) :
    (toPhys (freqTrR (complexify g)) : Space → Space) =ᵐ[volume] g := by
  have e : toPhys (freqTrR (complexify g)) = realPart (complexify g) := by
    show realPart (freqTrL2.symm (freqTrL2 (complexify g))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [e]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec (complexify g),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec g] with x e1 e2
  rw [realPart, e1, complexify, e2]
  ext i
  simp [realVec, complexifyVec]

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
    show ‖c • z‖ ≤ ‖c‖ * ‖z‖
    rw [norm_smul]

theorem continuous_cmul : Continuous cmul :=
  continuous_clm_apply.2 fun z => by
    show Continuous fun c : ℂ => c • z
    fun_prop

theorem coord_div_norm_le (ξ : Space) (k : Fin 3) : ‖((ξ k : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ)‖ ≤ 1 := by
  have hk : |ξ k| ≤ ‖ξ‖ := by
    have := PiLp.norm_apply_le ξ k
    simpa [Real.norm_eq_abs] using this
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, norm_norm]
  exact div_le_one_of_le₀ hk (norm_nonneg _)

theorem symbol_ae (h1 : FieldOpRealized) (s : Space → ℂ) (hs : Measurable s) (hb : ∀ ξ, ‖s ξ‖ ≤ 1)
    (g : L2C) :
    (fieldOp id (fun ξ => cmul (s ξ)) g : Space → CSpace) =ᵐ[volume] fun ξ => s ξ • g ξ :=
  h1 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (s ξ)) 1
    (continuous_cmul.comp_aestronglyMeasurable hs.aestronglyMeasurable)
    (fun ξ => (norm_cmul_le _).trans (hb ξ)) g

theorem gradSymbol_ae (h1 : FieldOpRealized) (k : Fin 3) (g : L2C) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g : Space → CSpace) =ᵐ[volume]
      fun ξ => gradSymbol k ξ • g ξ :=
  symbol_ae h1 _ (by unfold gradSymbol; fun_prop) (fun ξ => by
    unfold gradSymbol
    rw [norm_neg, mul_div_assoc, norm_mul, Complex.norm_I, one_mul]
    exact coord_div_norm_le ξ k) g

theorem derivSymbol_ae (h1 : FieldOpRealized) (k : Fin 3) (g : L2C) :
    (fieldOp id (fun ξ => cmul (derivSymbol k ξ)) g : Space → CSpace) =ᵐ[volume]
      fun ξ => derivSymbol k ξ • g ξ :=
  symbol_ae h1 _ (by unfold derivSymbol; fun_prop) (fun ξ => by
    unfold derivSymbol
    rw [mul_div_assoc, norm_mul, Complex.norm_I, one_mul]
    exact coord_div_norm_le ξ k) g

theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
  exact measure_singleton _

theorem norm_sq_eq (ξ : Space) : ‖ξ‖ ^ 2 = ∑ k, (ξ k) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp

theorem integrable_rapid_smul (g : 𝓢(Space, ℂ)) {w : Space → CSpace} (hw : MemLp w 2 volume) :
    Integrable (fun x => g x • w x) volume := by
  have h : MemLp ((g : Space → ℂ) • w) 1 volume := hw.smul (g.memLp 2 volume)
  exact memLp_one_iff_integrable.1 h

theorem coe_complexify_ae (g : L2R) :
    (complexify g : Space → CSpace) =ᵐ[volume] fun x => complexifyVec (g x) :=
  ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec g

theorem complexify_toLp_ae {f : Space → Space} (hf : MemLp f 2 volume) :
    (complexify (toLpOrZero 2 f) : Space → CSpace) =ᵐ[volume] fun x => complexifyVec (f x) := by
  filter_upwards [coe_complexify_ae (toLpOrZero 2 f), toLpOrZero_ae hf] with x h1 h2
  rw [h1, h2]

theorem memLp_complexify {f : Space → Space} (hf : MemLp f 2 volume) :
    MemLp (fun x => complexifyVec (f x)) 2 volume :=
  complexifyVec.comp_memLp' hf

theorem lineDeriv_eq {f : Space → Space} (hf : IsH1Field f) (k : Fin 3) :
    ∂_{unitVector k} (Lp.toTemperedDistribution (complexify (toLpOrZero 2 f))) =
      Lp.toTemperedDistribution (complexify (toLpOrZero 2 (partialField f k))) := by
  obtain ⟨hs, -, hf2, hd2⟩ := hf
  ext1 g
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have e1 : ∫ x, (-∂_{unitVector k} g) x • (complexify (toLpOrZero 2 f) : Space → CSpace) x =
      ∫ x, (-∂_{unitVector k} g) x • complexifyVec (f x) := by
    apply integral_congr_ae
    filter_upwards [complexify_toLp_ae hf2] with x hx
    rw [hx]
  have e2 : ∫ x, g x • (complexify (toLpOrZero 2 (partialField f k)) : Space → CSpace) x =
      ∫ x, g x • complexifyVec (partialField f k x) := by
    apply integral_congr_ae
    filter_upwards [complexify_toLp_ae (hd2 k)] with x hx
    rw [hx]
  rw [e1, e2]
  have hdiff : Differentiable ℝ f := hs.differentiable (by simp)
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (v := unitVector k)
    (B := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] CSpace →L[ℝ] CSpace))
    (f := fun x => g x) (f' := fun x => ∂_{unitVector k} g x)
    (g := fun x => complexifyVec (f x)) (g' := fun x => complexifyVec (partialField f k x))
    (integrable_rapid_smul _ (memLp_complexify hf2))
    (integrable_rapid_smul _ (memLp_complexify (hd2 k)))
    (integrable_rapid_smul _ (memLp_complexify hf2))
    (fun x _ => by
      rw [SchwartzMap.lineDerivOp_apply]
      exact (g.differentiableAt).lineDifferentiableAt.hasLineDerivAt)
    (fun x _ => ((complexifyVec.hasFDerivAt.comp x (hdiff x).hasFDerivAt).hasLineDerivAt (unitVector k)))
  simp only [ContinuousLinearMap.lsmul_apply] at key
  rw [key]
  simp [integral_neg]

theorem ae_zero_of_rapid {w : Space → CSpace} (hw : LocallyIntegrable w volume)
    (h : ∀ g : 𝓢(Space, ℂ), ∫ x, g x • w x = 0) : ∀ᵐ x ∂volume, w x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hw
  intro g g_smooth g_cpt
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  rw [← h (hg₁.toSchwartzMap hg₂)]
  congr 1

theorem freqTr_partial_ae {f : Space → Space} (hf : IsH1Field f) (k : Fin 3) :
    (freqTrR (complexify (toLpOrZero 2 (partialField f k))) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) •
        (freqTrR (complexify (toLpOrZero 2 f)) : Space → CSpace) ξ := by
  set U := complexify (toLpOrZero 2 f) with hU
  set V := complexify (toLpOrZero 2 (partialField f k)) with hV
  have hD := congrArg (fun T => 𝓕 T) (lineDeriv_eq hf k)
  rw [TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at hD
  have hc : Continuous (fun ξ : Space => (2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) := by fun_prop
  have hloc : LocallyIntegrable (fun ξ => ((𝓕 V : L2C) : Space → CSpace) ξ -
      ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • ((𝓕 U : L2C) : Space → CSpace) ξ) volume :=
    ((Lp.memLp _).locallyIntegrable (by norm_num)).sub
      (((Lp.memLp _).locallyIntegrable (by norm_num)).continuous_smul hc)
  have hz := ae_zero_of_rapid hloc (fun g => ?_)
  · filter_upwards [hz] with ξ hξ
    exact sub_eq_zero.1 hξ
  have hg := congrArg (fun T => T g) hD
  simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply] at hg
  rw [SchwartzMap.smulLeftCLM_apply (by fun_prop)] at hg
  rw [← hU, ← hV] at hg
  have hin : ∀ x : Space, inner ℝ x (unitVector k) = x k := fun x => by
    rw [unitVector, EuclideanSpace.inner_single_right]
    simp
  simp only [hin] at hg
  have hi1 : Integrable (fun x => g x • ((𝓕 V : L2C) : Space → CSpace) x) :=
    integrable_rapid_smul g (Lp.memLp _)
  have hi2 : Integrable (fun x => (((x k : ℝ) : ℂ) • g x) • ((𝓕 U : L2C) : Space → CSpace) x) := by
    have := integrable_rapid_smul
      (SchwartzMap.smulLeftCLM ℂ (fun x : Space => ((inner ℝ x (unitVector k) : ℝ) : ℂ)) g)
      (Lp.memLp (𝓕 U : L2C))
    rw [SchwartzMap.smulLeftCLM_apply (by fun_prop)] at this
    simpa only [hin] using this
  have hpt : ∀ x, g x • (((𝓕 V : L2C) : Space → CSpace) x -
      (2 * π * Complex.I * ((x k : ℝ) : ℂ)) • ((𝓕 U : L2C) : Space → CSpace) x) =
      g x • ((𝓕 V : L2C) : Space → CSpace) x -
        (2 * π * Complex.I) • ((((x k : ℝ) : ℂ) • g x) • ((𝓕 U : L2C) : Space → CSpace) x) := fun x => by
    simp only [smul_sub, smul_smul, smul_eq_mul]
    congr 2
    ring
  have hi3 : Integrable (fun x => (2 * π * Complex.I) •
      ((((x k : ℝ) : ℂ) • g x) • ((𝓕 U : L2C) : Space → CSpace) x)) := by
    convert hi2.smul (2 * π * Complex.I) using 1 <;> rfl
  simp_rw [hpt]
  rw [integral_sub hi1 hi3, integral_smul, hg, sub_self]

theorem ae_zero_of_rapid_scalar {w : Space → ℂ} (hw : LocallyIntegrable w volume)
    (h : ∀ g : 𝓢(Space, ℂ), ∫ x, g x • w x = 0) : ∀ᵐ x ∂volume, w x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hw
  intro g g_smooth g_cpt
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  rw [← h (hg₁.toSchwartzMap hg₂)]
  congr 1

theorem integral_freqTr_swap (V : L2C) (g : 𝓢(Space, ℂ)) :
    ∫ x, g x • ((𝓕 V : L2C) : Space → CSpace) x = ∫ x, (𝓕 g) x • (V : Space → CSpace) x := by
  have h := congrArg (fun T => T g) (Lp.fourier_toTemperedDistribution_eq V)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h
  exact h.symm

theorem integral_coord (h : Space → CSpace) (hh : Integrable h volume) (i : Fin 3) :
    ∫ x, (h x) i = (∫ x, h x) i :=
  (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integral_comp_comm hh

theorem div_freqTr_ae {f : Space → Space} (hf : IsH1Field f) :
    ∀ᵐ ξ ∂volume, ∑ i : Fin 3,
      (freqTrR (complexify (toLpOrZero 2 (partialField f i))) : Space → CSpace) ξ i = 0 := by
  obtain ⟨-, hdiv, -, hd2⟩ := hf
  set V : Fin 3 → L2C := fun i => complexify (toLpOrZero 2 (partialField f i)) with hVdef
  have hloc : ∀ i : Fin 3, LocallyIntegrable (fun ξ => ((𝓕 (V i) : L2C) : Space → CSpace) ξ i) volume :=
    fun i => (((EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).comp_memLp' (Lp.memLp (𝓕 (V i) : L2C))).locallyIntegrable
      (by norm_num))
  apply ae_zero_of_rapid_scalar (locallyIntegrable_finsetSum _ (fun i _ => hloc i))
  intro g
  have step : ∀ i : Fin 3, ∫ ξ, g ξ • ((𝓕 (V i) : L2C) : Space → CSpace) ξ i =
      ∫ x, (𝓕 g) x • (V i : Space → CSpace) x i := by
    intro i
    have e1 := integral_coord (fun ξ => g ξ • ((𝓕 (V i) : L2C) : Space → CSpace) ξ)
      (integrable_rapid_smul g (Lp.memLp _)) i
    have e2 := integral_coord (fun x => (𝓕 g) x • (V i : Space → CSpace) x)
      (integrable_rapid_smul _ (Lp.memLp _)) i
    simp only [PiLp.smul_apply] at e1 e2
    rw [e1, e2, integral_freqTr_swap]
  have hint : ∀ i : Fin 3, Integrable (fun x => (𝓕 g) x • (V i : Space → CSpace) x i) volume := by
    intro i
    have := (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integrable_comp
      (integrable_rapid_smul (𝓕 g) (Lp.memLp (V i)))
    exact this
  have hint2 : ∀ i : Fin 3, Integrable (fun ξ => g ξ • ((𝓕 (V i) : L2C) : Space → CSpace) ξ i) volume := by
    intro i
    exact (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integrable_comp
      (integrable_rapid_smul g (Lp.memLp (𝓕 (V i) : L2C)))
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun i _ => hint2 i), Finset.sum_congr rfl (fun i _ => step i),
    ← integral_finsetSum _ (fun i _ => hint i)]
  have hae : ∀ i : Fin 3, (V i : Space → CSpace) =ᵐ[volume] fun x => complexifyVec (partialField f i x) :=
    fun i => complexify_toLp_ae (hd2 i)
  rw [integral_eq_zero_of_ae]
  filter_upwards [ae_all_iff.2 hae] with x hx
  simp only [Pi.zero_apply]
  rw [← Finset.smul_sum]
  simp only [hx]
  have hd := hdiv x
  unfold divergenceAt at hd
  have : ∑ i : Fin 3, (complexifyVec (partialField f i x)) i = ((∑ i : Fin 3, (fderiv ℝ f x (unitVector i)) i : ℝ) : ℂ) := by
    simp [complexifyVec, partialField]
  rw [this, hd]
  simp

theorem norm_freqVec (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, freqVec, complexifyVec]

theorem longitudinal_apply (ξ : Space) (z : CSpace) :
    longitudinal ξ z = ((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ) z • freqVec ξ) := rfl

theorem norm_longitudinal_le (ξ : Space) : ‖longitudinal ξ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [longitudinal_apply, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (‖ξ‖ ^ 2)⁻¹ * (‖inner ℂ (freqVec ξ) z‖ * ‖freqVec ξ‖)
        ≤ (‖ξ‖ ^ 2)⁻¹ * (‖freqVec ξ‖ * ‖z‖ * ‖freqVec ξ‖) := by
          gcongr
          exact norm_inner_le_norm _ _
      _ = ((‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2) * ‖z‖ := by rw [norm_freqVec]; ring
      _ ≤ 1 * ‖z‖ := by
          gcongr
          rcases eq_or_ne ‖ξ‖ 0 with h | h
          · simp [h]
          · rw [inv_mul_cancel₀ (pow_ne_zero _ h)]

theorem aesm_longitudinal : AEStronglyMeasurable longitudinal volume := by
  have hL : Continuous fun ξ : Space =>
      ((ContinuousLinearMap.smulRight (innerSL ℂ (freqVec ξ)) (freqVec ξ)).restrictScalars ℝ :
        CSpace →L[ℝ] CSpace) :=
    continuous_clm_apply.2 fun z => by
      show Continuous fun ξ : Space => inner ℂ (freqVec ξ) z • freqVec ξ
      have hv : Continuous freqVec := complexifyVec.continuous
      fun_prop
  have hm : Measurable fun ξ : Space => ((‖ξ‖ ^ 2)⁻¹ : ℝ) := by fun_prop
  exact hm.aestronglyMeasurable.smul hL.aestronglyMeasurable

theorem longitudinal_ae (h1 : FieldOpRealized) (g : L2C) :
    (fieldOp id longitudinal g : Space → CSpace) =ᵐ[volume] fun ξ => longitudinal ξ (g ξ) :=
  h1 (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1 aesm_longitudinal norm_longitudinal_le g

theorem reflConj_ae (h1 : FieldOpRealized) (g : L2C) :
    (reflConj g : Space → CSpace) =ᵐ[volume] fun ξ => conjVec (g (-ξ)) :=
  h1 (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖ aestronglyMeasurable_const
    (fun _ => le_rfl) g

theorem ae_comp_neg {β : Type*} {u v : Space → β} (h : u =ᵐ[volume] v) :
    (fun ξ => u (-ξ)) =ᵐ[volume] fun ξ => v (-ξ) :=
  (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp h

theorem mem_sig_iff (h : L2C) : h ∈ Sig ↔ reflConj h = h ∧ fieldOp id longitudinal h = 0 := by
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]

theorem mem_sig_of_ae (h1 : FieldOpRealized) {s h : L2C} (hs : s ∈ Sig) (ρ : Space → ℝ)
    (hρ : ∀ ξ, ρ (-ξ) = ρ ξ) (hh : (h : Space → CSpace) =ᵐ[volume] fun ξ => ρ ξ • s ξ) : h ∈ Sig := by
  rw [mem_sig_iff] at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · apply Lp.ext
    have hsr := reflConj_ae h1 s
    rw [hs1] at hsr
    filter_upwards [reflConj_ae h1 h, ae_comp_neg hh, hsr, hh] with ξ e1 e2 e3 e4
    rw [e1, e2, e4, hρ, map_smul, e3]
  · apply Lp.ext
    have hsl := longitudinal_ae h1 s
    rw [hs2] at hsl
    filter_upwards [longitudinal_ae h1 h, hh, hsl, Lp.coeFn_zero CSpace 2 (volume : Measure Space)]
      with ξ e1 e2 e3 e4
    rw [e1, e2, map_smul, ← e3, e4]
    simp

theorem grad_term (a n : ℂ) :
    -(Complex.I * a / n) * (2 * π * Complex.I * a) = 2 * π * a ^ 2 / n := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem grad_sum (ξ : Space) (hξ : ξ ≠ 0) :
    ∑ k : Fin 3, gradSymbol k ξ * (2 * π * Complex.I * ((ξ k : ℝ) : ℂ)) =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) := by
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hξ)
  have hn2 : ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ∑ k, ((ξ k : ℝ) : ℂ) ^ 2 := by exact_mod_cast norm_sq_eq ξ
  unfold gradSymbol
  simp_rw [grad_term]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← hn2]
  push_cast
  field_simp

theorem deriv_mul (j : Fin 3) (ξ : Space) (hξ : ξ ≠ 0) :
    derivSymbol j ξ * (((2 * π * ‖ξ‖ : ℝ)) : ℂ) = 2 * π * Complex.I * ((ξ j : ℝ) : ℂ) := by
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hξ)
  unfold derivSymbol
  push_cast
  field_simp

theorem coe_sum_three (S : Fin 3 → L2C) :
    ((∑ k, S k : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => ∑ k, (S k : Space → CSpace) ξ := by
  rw [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (S 0 + S 1) (S 2), Lp.coeFn_add (S 0) (S 1)] with ξ e1 e2
  rw [e1, Pi.add_apply, e2, Pi.add_apply, Fin.sum_univ_three]

theorem ofGrad_ae (h1 : FieldOpRealized) {f : Space → Space} (hf : IsH1Field f) :
    (ofGrad f : Space → CSpace) =ᵐ[volume]
      fun ξ => (2 * π * ‖ξ‖) • (freqTrR (complexify (toLpOrZero 2 f)) : Space → CSpace) ξ := by
  filter_upwards [coe_sum_three (fun k => fieldOp id (fun ξ => cmul (gradSymbol k ξ))
      (freqTrR (complexify (toLpOrZero 2 (partialField f k))))),
    ae_all_iff.2 (fun k => gradSymbol_ae h1 k (freqTrR (complexify (toLpOrZero 2 (partialField f k))))),
    ae_all_iff.2 (fun k => freqTr_partial_ae hf k), ae_ne_zero] with ξ e1 e2 e3 hξ
  rw [ofGrad, e1]
  simp_rw [e2, e3, smul_smul, ← Finset.sum_smul, grad_sum ξ hξ, Complex.coe_smul]

theorem hat_mem_sig (h1 : FieldOpRealized) (h2 : FreqTrConjSym) {f : Space → Space}
    (hf : IsH1Field f) : freqTrR (complexify (toLpOrZero 2 f)) ∈ Sig := by
  rw [mem_sig_iff]
  refine ⟨h2 _, ?_⟩
  apply Lp.ext
  filter_upwards [longitudinal_ae h1 (freqTrR (complexify (toLpOrZero 2 f))),
    Lp.coeFn_zero CSpace 2 (volume : Measure Space), div_freqTr_ae hf,
    ae_all_iff.2 (fun k => freqTr_partial_ae hf k)] with ξ e1 e2 e3 e4
  rw [e1, e2, longitudinal_apply]
  simp only [e4, PiLp.smul_apply, smul_eq_mul] at e3
  have hsum : ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) *
      (freqTrR (complexify (toLpOrZero 2 f)) : Space → CSpace) ξ i = 0 := by
    have h' : (2 * π * Complex.I) * ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) *
        (freqTrR (complexify (toLpOrZero 2 f)) : Space → CSpace) ξ i = 0 := by
      rw [← e3, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    exact (mul_eq_zero.1 h').resolve_left (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  have hinner : inner ℂ (freqVec ξ) ((freqTrR (complexify (toLpOrZero 2 f)) : Space → CSpace) ξ) = 0 := by
    rw [← hsum, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [freqVec, complexifyVec, mul_comm]
  rw [hinner]
  simp

end Internal.H1Consistency

open Internal.H1Consistency in
theorem h1Consistency (h1 : FieldOpRealized) (h2 : FreqTrConjSym) (h3 : VelocityInvertsHalfSsp) :
    H1Consistency := by
  intro f hf
  have hs := hat_mem_sig h1 h2 hf
  have hog := ofGrad_ae h1 hf
  have hmem : ofGrad f ∈ Sig := mem_sig_of_ae h1 hs (fun ξ => 2 * π * ‖ξ‖) (fun ξ => by simp) hog
  have hemb : (embedX f : L2C) = ofGrad f := by rw [embedX, dif_pos hmem]
  refine ⟨hmem, ?_, fun j => ?_⟩
  · have hhalf : IsHalfSspOf ⟨_, hs⟩ (embedX f) := by
      unfold IsHalfSspOf
      rw [hemb]
      exact hog
    filter_upwards [h3 _ _ hhalf, toPhys_freqTr_complexify (toLpOrZero 2 f), toLpOrZero_ae hf.2.2.1]
      with x e1 e2 e3
    exact e1.trans (e2.trans e3)
  · have heq : fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (ofGrad f) =
        freqTrR (complexify (toLpOrZero 2 (partialField f j))) := by
      apply Lp.ext
      filter_upwards [derivSymbol_ae h1 j (ofGrad f), hog, freqTr_partial_ae hf j, ae_ne_zero]
        with ξ e1 e2 e3 hξ
      rw [e1, e2, e3, ← Complex.coe_smul, smul_smul, deriv_mul j ξ hξ]
    have hp : partialX j (embedX f) = toPhys (freqTrR (complexify (toLpOrZero 2 (partialField f j)))) := by
      show toPhys (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (embedX f : L2C)) = _
      rw [hemb, heq]
    rw [hp]
    exact (toPhys_freqTr_complexify _).trans (toLpOrZero_ae (hf.2.2.2 j))

end Breakdown.Freq
