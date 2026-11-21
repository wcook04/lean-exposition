import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

open LineDeriv FourierTransform SchwartzMap

namespace Internal.EmbedNegSsp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def pd (f : Space → F) (k : Fin 3) : Space → F := fun x => fderiv ℝ f x (unitVector k)

theorem contDiff_pd {f : Space → F} (hf : ContDiff ℝ ∞ f) (k : Fin 3) : ContDiff ℝ ∞ (pd f k) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem differentiable_of_smooth {f : Space → F} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem pd_neg (f : Space → F) (k : Fin 3) : pd (fun x => -f x) k = fun x => -pd f k x := by
  funext x
  simp [pd]

theorem pd_sum {ι : Type*} (s : Finset ι) (g : ι → Space → F) (hg : ∀ i, Differentiable ℝ (g i))
    (k : Fin 3) : pd (fun x => ∑ i ∈ s, g i x) k = fun x => ∑ i ∈ s, pd (g i) k x := by
  funext x
  simp only [pd]
  rw [fderiv_fun_sum (fun i _ => (hg i) x)]
  simp

theorem pd_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G)
    {g : Space → F} (hg : Differentiable ℝ g) (k : Fin 3) :
    pd (fun x => L (g x)) k = fun x => L (pd g k x) := by
  funext x
  show fderiv ℝ (L ∘ g) x (unitVector k) = _
  rw [((L.hasFDerivAt).comp x (hg x).hasFDerivAt).fderiv]
  rfl

theorem pd_pd {f : Space → F} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (x : Space) :
    pd (pd f i) j x = fderiv ℝ (fderiv ℝ f) x (unitVector j) (unitVector i) := by
  show fderiv ℝ (fun y => fderiv ℝ f y (unitVector i)) x (unitVector j) = _
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  rw [fderiv_clm_apply h1 (differentiableAt_const _)]
  simp

theorem pd_comm {f : Space → F} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) :
    pd (pd f i) j = pd (pd f j) i := by
  funext x
  rw [pd_pd hf, pd_pd hf]
  exact ((contDiff_infty.1 hf 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem sumSecondPartialsAt_eq {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x : Space) :
    sumSecondPartialsAt f x = ∑ i, pd (pd f i) i x := by
  simp only [sumSecondPartialsAt, iteratedFDeriv_two_apply, pd_pd hf]
  rfl

theorem negSsp_eq {f : Space → Space} (hf : ContDiff ℝ ∞ f) :
    negSsp f = fun x => -∑ j, pd (pd f j) j x := by
  funext x
  simp [negSsp, sumSecondPartialsAt_eq hf]

end Internal.EmbedNegSsp

namespace Internal.EmbedNegSsp

theorem hasCompactSupport_pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space → F}
    (hf : HasCompactSupport f) (k : Fin 3) : HasCompactSupport (pd f k) :=
  hf.fderiv_apply ℝ _

theorem pd_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : Fin 3) :
    pd (fun _ : Space => (0 : F)) k = fun _ => 0 := by
  funext x
  simp [pd]

def dv (g : Space → Space) : Space → ℝ := fun y => ∑ i, EuclideanSpace.proj i (pd g i y)

theorem divergenceAt_eq_dv (g : Space → Space) (y : Space) : divergenceAt g y = dv g y := by
  simp [divergenceAt, dv, pd]

theorem pd_dv {g : Space → Space} (hg : ContDiff ℝ ∞ g) (j : Fin 3) : pd (dv g) j = dv (pd g j) := by
  unfold dv
  rw [pd_sum Finset.univ (fun i y => EuclideanSpace.proj i (pd g i y)) (fun i => ((EuclideanSpace.proj i).differentiable.comp
    (differentiable_of_smooth (contDiff_pd hg i)) :))]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_clm (EuclideanSpace.proj i) (differentiable_of_smooth (contDiff_pd hg i)), pd_comm hg]

theorem dv_neg_sum {g : Fin 3 → Space → Space} (hg : ∀ j, ContDiff ℝ ∞ (g j)) :
    dv (fun x => -∑ j, g j x) = fun y => -∑ j, dv (g j) y := by
  funext y
  simp only [dv, pd_neg, pd_sum _ _ (fun j => differentiable_of_smooth (hg j)), map_neg, map_sum,
    Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

theorem isTestField_negSsp {φ : Space → Space} (h : IsTestField φ) : IsTestField (negSsp φ) := by
  have hs : ∀ j, ContDiff ℝ ∞ (pd (pd φ j) j) := fun j => contDiff_pd (contDiff_pd h.1 j) j
  rw [negSsp_eq h.1]
  refine ⟨(ContDiff.sum fun j _ => hs j).neg, ?_, ?_⟩
  · have e : (fun x => -∑ j, pd (pd φ j) j x) = -(∑ j, pd (pd φ j) j) := by
      funext x
      simp
    rw [e]
    exact (HasCompactSupport.finset_sum fun j _ =>
      hasCompactSupport_pd (hasCompactSupport_pd h.2.1 j) j).neg
  · intro y
    have h0 : dv φ = fun _ => 0 := by
      funext x
      rw [← divergenceAt_eq_dv]
      exact h.2.2 x
    rw [divergenceAt_eq_dv, dv_neg_sum hs]
    have e : ∀ j, dv (pd (pd φ j) j) = pd (pd (dv φ) j) j := by
      intro j
      rw [← pd_dv (contDiff_pd h.1 j), ← pd_dv h.1]
    simp [e, h0, pd_zero]

theorem isDecayField_of_isTestField {φ : Space → Space} (h : IsTestField φ) : IsDecayField φ := by
  refine ⟨h.1, h.2.2, ?_⟩
  have hc : Continuous fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) := by
    have h0 : Continuous φ := h.1.continuous
    have h1 : Continuous (fderiv ℝ φ) := h.1.continuous_fderiv (by simp)
    fun_prop
  have hk : HasCompactSupport fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) :=
    (h.2.1.norm.add (h.2.1.fderiv ℝ).norm).mul_left
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hk
  refine ⟨C, fun y => ?_⟩
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hy : (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) ≤ C := by
    have := hC y
    rwa [Real.norm_of_nonneg (by positivity)] at this
  have a := norm_nonneg (φ y)
  have b := norm_nonneg (fderiv ℝ φ y)
  have c := norm_nonneg y
  constructor
  · rw [le_div_iff₀ hp]
    nlinarith [mul_nonneg (mul_nonneg a c) hp.le, mul_nonneg b (sq_nonneg (1 + ‖y‖))]
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg a (sq_nonneg (1 + ‖y‖))]

end Internal.EmbedNegSsp

namespace Internal.EmbedNegSsp

theorem freqTr_pd_apply (S : 𝓢(Space, CSpace)) (k : Fin 3) (ξ : Space) :
    𝓕 (∂_{unitVector k} S) ξ = ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • 𝓕 S ξ := by
  have : (inner ℝ · (unitVector k)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (unitVector k)).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq, _root_.smul_apply, smulLeftCLM_apply_apply this,
    ← Complex.coe_smul, smul_smul]
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem coe_lineDeriv_eq {S : 𝓢(Space, CSpace)} {g : Space → Space} (hg : Differentiable ℝ g)
    (hS : ⇑S = fun x => complexifyVec (g x)) (k : Fin 3) :
    ⇑(∂_{unitVector k} S : 𝓢(Space, CSpace)) = fun x => complexifyVec (pd g k x) := by
  funext x
  rw [lineDerivOp_apply_eq_fderiv, hS]
  exact congrFun (pd_clm complexifyVec hg k) x

theorem realVec_complexifyVec (v : Space) : realVec (complexifyVec v) = v := by
  ext i
  simp [realVec, complexifyVec]

theorem complexify_toLpOrZero {S : 𝓢(Space, CSpace)} {h : Space → Space}
    (hS : ⇑S = fun x => complexifyVec (h x)) : complexify (toLpOrZero 2 h) = S.toLp 2 := by
  have hm : MemLp h 2 volume := by
    have e : h = ⇑realVec ∘ ⇑S := by
      funext x
      simp [hS, realVec_complexifyVec]
    rw [e]
    exact realVec.comp_memLp' (S.memLp 2)
  unfold toLpOrZero
  rw [dif_pos hm]
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (hm.toLp h),
    hm.coeFn_toLp, S.coeFn_toLp 2] with x h1 h2 h3
  change (ContinuousLinearMap.compLpL 2 volume complexifyVec (hm.toLp h) : Space → CSpace) x = _
  rw [h1, h2, h3, hS]

theorem freqTrR_toLp (S : 𝓢(Space, CSpace)) : freqTrR (S.toLp 2) = (𝓕 S).toLp 2 :=
  SchwartzMap.toLp_fourier_eq S

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by simp [cmul, norm_smul]

theorem norm_gradSymbol_le (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  simp only [gradSymbol, norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_norm]
  exact div_le_one_of_le₀ (by simpa using PiLp.norm_apply_le ξ k) (norm_nonneg _)

theorem gradOp_ae (h1 : FieldOpRealized) (k : Fin 3) (f : L2C) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) f : Space → CSpace) =ᵐ[volume]
      fun ξ => cmul (gradSymbol k ξ) (f ξ) := by
  have e : (fun ξ => cmul (gradSymbol k ξ)) =
      fun ξ => gradSymbol k ξ • ContinuousLinearMap.id ℝ CSpace := by
    funext ξ
    ext1 v
    simp [cmul]
  have hm : Measurable (gradSymbol k) := by
    unfold gradSymbol
    fun_prop
  have hr := h1 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1
    (by rw [e]; exact (hm.smul_const _).aestronglyMeasurable)
    (fun ξ => (norm_cmul_le _).trans (norm_gradSymbol_le k ξ))
  rw [ContinuousLinearEquiv.coe_refl'] at hr
  exact hr f

theorem coeFn_sum_three (A : Fin 3 → L2C) :
    ((∑ k, A k : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => ∑ k, (A k : Space → CSpace) ξ := by
  rw [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (A 0 + A 1) (A 2), Lp.coeFn_add (A 0) (A 1)] with ξ h h'
  rw [h, Pi.add_apply, h', Pi.add_apply, Fin.sum_univ_three]

theorem ofGrad_ae (h1 : FieldOpRealized) {f : Space → Space} {T : Fin 3 → 𝓢(Space, CSpace)}
    (hT : ∀ k, ⇑(T k) = fun x => complexifyVec (pd f k x)) :
    (ofGrad f : Space → CSpace) =ᵐ[volume] fun ξ => ∑ k, cmul (gradSymbol k ξ) (𝓕 (T k) ξ) := by
  have e : ofGrad f = ∑ k, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) ((𝓕 (T k)).toLp 2) := by
    unfold ofGrad
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show partialField f k = pd f k from rfl, complexify_toLpOrZero (hT k), freqTrR_toLp]
  have hr : ∀ᵐ ξ ∂volume, ∀ k, (fieldOp id (fun ξ => cmul (gradSymbol k ξ))
      ((𝓕 (T k)).toLp 2) : Space → CSpace) ξ = cmul (gradSymbol k ξ) (𝓕 (T k) ξ) := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [gradOp_ae h1 k ((𝓕 (T k)).toLp 2), (𝓕 (T k)).coeFn_toLp 2] with ξ a b
    rw [a, b]
  rw [e]
  filter_upwards [coeFn_sum_three _, hr] with ξ hs hk
  rw [hs]
  exact Finset.sum_congr rfl fun k _ => hk k

end Internal.EmbedNegSsp

namespace Internal.EmbedNegSsp

theorem ssp_scalar (ξ : Space) (k : Fin 3) :
    -∑ j, ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) *
      (((2 * π * Complex.I) * ((ξ j : ℝ) : ℂ)) * ((2 * π * Complex.I) * ((ξ j : ℝ) : ℂ))) =
      ((sspFactor ξ : ℝ) : ℂ) * ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) := by
  have hn : ‖ξ‖ ^ 2 = ∑ j, ξ j ^ 2 := EuclideanSpace.real_norm_sq_eq ξ
  simp only [sspFactor, hn, Fin.sum_univ_three]
  push_cast
  linear_combination (-8 * (π : ℂ) ^ 3 * Complex.I * ((ξ k : ℝ) : ℂ) *
    (((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2)) * Complex.I_sq

theorem ofGrad_negSsp_ae (h1 : FieldOpRealized) {φ : Space → Space} (hφ : IsTestField φ) :
    ∀ᵐ ξ ∂volume, (ofGrad (negSsp φ) : Space → CSpace) ξ =
      sspFactor ξ • (ofGrad φ : Space → CSpace) ξ := by
  have hsm : ContDiff ℝ ∞ (fun x => complexifyVec (φ x)) := complexifyVec.contDiff.comp hφ.1
  have hcs : HasCompactSupport (fun x => complexifyVec (φ x)) :=
    hφ.2.1.comp_left (map_zero complexifyVec)
  set Φ : 𝓢(Space, CSpace) := hcs.toSchwartzMap hsm
  have hΦ : ⇑Φ = fun x => complexifyVec (φ x) := rfl
  have d0 := differentiable_of_smooth hφ.1
  have d1 : ∀ j, Differentiable ℝ (pd φ j) := fun j => differentiable_of_smooth (contDiff_pd hφ.1 j)
  have d2 : ∀ j, Differentiable ℝ (pd (pd φ j) j) := fun j =>
    differentiable_of_smooth (contDiff_pd (contDiff_pd hφ.1 j) j)
  have c1 : ∀ j, ⇑(∂_{unitVector j} Φ : 𝓢(Space, CSpace)) = fun x => complexifyVec (pd φ j x) :=
    coe_lineDeriv_eq d0 hΦ
  have c2 : ∀ j, ⇑(∂_{unitVector j} (∂_{unitVector j} Φ) : 𝓢(Space, CSpace)) =
      fun x => complexifyVec (pd (pd φ j) j x) := fun j => coe_lineDeriv_eq (d1 j) (c1 j) j
  have c3 : ∀ j k, ⇑(∂_{unitVector k} (∂_{unitVector j} (∂_{unitVector j} Φ)) : 𝓢(Space, CSpace)) =
      fun x => complexifyVec (pd (pd (pd φ j) j) k x) := fun j k => coe_lineDeriv_eq (d2 j) (c2 j) k
  let T : Fin 3 → 𝓢(Space, CSpace) := fun k => ∂_{unitVector k} Φ
  let U : Fin 3 → 𝓢(Space, CSpace) := fun k =>
    -∑ j, (∂_{unitVector k} (∂_{unitVector j} (∂_{unitVector j} Φ)) : 𝓢(Space, CSpace))
  have hU : ∀ k, ⇑(U k) = fun x => complexifyVec (pd (negSsp φ) k x) := by
    intro k
    funext x
    rw [negSsp_eq hφ.1, pd_neg, pd_sum _ _ d2]
    simp [U, c3]
  have hF : ∀ k ξ, 𝓕 (U k) ξ = sspFactor ξ • 𝓕 (T k) ξ := by
    intro k ξ
    simp only [U, T, FourierTransform.fourier_neg, fourier_sum, _root_.neg_apply, _root_.sum_apply,
      freqTr_pd_apply, smul_smul]
    rw [← Complex.coe_smul, smul_smul, ← Finset.sum_smul, ← neg_smul, ssp_scalar]
  filter_upwards [ofGrad_ae h1 (T := U) hU, ofGrad_ae h1 (T := T) c1] with ξ a b
  rw [a, b, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hF, ContinuousLinearMap.map_smul]

end Internal.EmbedNegSsp

theorem embedNegSsp (h1 : FieldOpRealized) (h2 : EmbedMem) :
    EmbedNegSsp := by
  intro φ hφ
  have a := h2 _ (Internal.EmbedNegSsp.isDecayField_of_isTestField hφ)
  have b := h2 _ (Internal.EmbedNegSsp.isDecayField_of_isTestField (Internal.EmbedNegSsp.isTestField_negSsp hφ))
  unfold IsSspOf embedX
  rw [dif_pos a, dif_pos b]
  exact Internal.EmbedNegSsp.ofGrad_negSsp_ae h1 hφ

end Breakdown.Freq
