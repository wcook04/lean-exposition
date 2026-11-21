import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.DriftSymbolWeak
import Breakdown.Frac.NNicePairing
import Breakdown.Uniqueness.RegPhysAuxProduct

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform SchwartzMap LineDeriv

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow Breakdown.SteadyCert

namespace Internal.ResidualGradient

theorem conjVec_smul (c : ℂ) (z : CSpace) : conjVec (c • z) = (starRingEnd ℂ c) • conjVec z := by
  ext i
  simp [conjVec]

theorem conj_invTransform {f : Space → CSpace} (hf : Integrable f) (hh : ∀ ξ, f (-ξ) = conjVec (f ξ))
    (y : Space) : conjVec (𝓕⁻ f y) = 𝓕⁻ f y := by
  rw [Real.fourierInv_eq, ← conjVec.integral_comp_comm (integrable_char_smul hf y)]
  calc ∫ v, conjVec (𝐞 (inner ℝ v y) • f v) = ∫ v, 𝐞 (inner ℝ (-v) y) • f (-v) := by
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        simp only
        rw [hh v, Circle.smul_def, Circle.smul_def, conjVec_smul, inner_neg_left,
          AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
    _ = ∫ v, 𝐞 (inner ℝ v y) • f v := integral_neg_eq_self (fun v => 𝐞 (inner ℝ v y) • f v) volume

theorem re_inner_realVec (z w : CSpace) (hw : conjVec w = w) :
    inner ℝ (realVec z) (realVec w) = RCLike.re (inner ℂ z w) := by
  have him : ∀ i, (w i).im = 0 := fun i => by
    have := congrArg (fun v : CSpace => v i) hw
    simp only [conjVec] at this
    exact Complex.conj_eq_iff_im.1 this
  simp [realVec, PiLp.inner_apply, Fin.sum_univ_three, Complex.mul_re, him]

set_option maxHeartbeats 1000000 in
theorem pair_symbol {h : Space → CSpace} (hh : Integrable h) (Ψ : 𝓢(Space, CSpace))
    (hΨ : ∀ ξ, Ψ (-ξ) = conjVec (Ψ ξ)) :
    ∫ y, inner ℝ (physField h y) (realVec ((𝓕⁻ Ψ) y)) = ∫ ξ, inner ℝ (h ξ) (Ψ ξ) := by
  set G : 𝓢(Space, CSpace) := 𝓕⁻ Ψ with hGdef
  have hG : ∀ y, conjVec (G y) = G y := fun y => by
    rw [hGdef, SchwartzMap.fourierInv_coe]
    exact conj_invTransform (Ψ.integrable (μ := volume)) hΨ y
  have hB : ∀ y, ‖𝓕⁻ h y‖ ≤ ∫ ξ, ‖h ξ‖ := fun y =>
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (-innerₗ Space) h y
  have hLc : Continuous fun p : Space × Space => (-innerₗ Space) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    exact (continuous_fst.inner continuous_snd).neg
  have hFc : Continuous (𝓕⁻ h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hLc hh
  have hI : Integrable (fun y => inner ℂ (𝓕⁻ h y) (G y)) := by
    refine ((G.integrable (μ := volume)).norm.const_mul (∫ ξ, ‖h ξ‖)).mono'
      (hFc.inner G.continuous).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
  have hI2 : Integrable (fun ξ => inner ℂ (h ξ) (Ψ ξ)) := by
    refine (hh.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 Ψ)).mono'
      (hh.aestronglyMeasurable.inner Ψ.continuous.aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ Ψ ξ) (norm_nonneg _)
  have key := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    Real.continuous_fourierChar hLc hh (G.integrable (μ := volume))
  have e3 : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (-(-innerₗ Space).flip) G x = Ψ x := by
    intro x
    have h0 : 𝓕 (G : Space → CSpace) x = Ψ x := by
      rw [← SchwartzMap.fourier_coe, hGdef, FourierTransform.fourier_fourierInv_eq]
    rw [← h0, Real.fourier_eq]
    simp only [VectorFourier.fourierIntegral, LinearMap.neg_apply, LinearMap.flip_apply, neg_neg,
      innerₗ_apply_apply]
    congr 1
    funext v
    rw [real_inner_comm]
  simp only [innerSL_apply_apply, e3] at key
  calc ∫ y, inner ℝ (physField h y) (realVec ((𝓕⁻ Ψ) y))
      = ∫ y, RCLike.re (inner ℂ (𝓕⁻ h y) (G y)) :=
        integral_congr_ae (ae_of_all _ fun y => re_inner_realVec _ _ (hG y))
    _ = RCLike.re (∫ y, inner ℂ (𝓕⁻ h y) (G y)) := integral_re hI
    _ = RCLike.re (∫ ξ, inner ℂ (h ξ) (Ψ ξ)) := by
        congr 1
    _ = ∫ ξ, RCLike.re (inner ℂ (h ξ) (Ψ ξ)) := (integral_re hI2).symm
    _ = ∫ ξ, inner ℝ (h ξ) (Ψ ξ) :=
        integral_congr_ae (ae_of_all _ fun ξ => (real_inner_eq_re_inner ℂ _ _).symm)

theorem inner_freqVec_zero {z : CSpace} {ξ : Space} (hz : ∑ i, ((ξ i : ℝ) : ℂ) * z i = 0) (d : ℂ) :
    inner ℝ z (d • freqVec ξ) = 0 := by
  rw [show inner ℝ z (d • freqVec ξ) = RCLike.re (inner ℂ z (d • freqVec ξ)) from
    real_inner_eq_re_inner ℂ _ _, inner_smul_right]
  have e : inner ℂ z (freqVec ξ) = starRingEnd ℂ (∑ i, ((ξ i : ℝ) : ℂ) * z i) := by
    simp [freqVec, complexifyVec, PiLp.inner_apply, map_sum, mul_comm]
  rw [e, hz, map_zero, mul_zero, map_zero]

open Breakdown.Freq.Internal.NicePairing Breakdown.SteadyCert.Internal.DriftSymbolWeakLinear in
theorem transport_pair {v : Space → Space} (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC0 : ∀ y, ‖v y‖ ≤ C)
    (hC1 : ∀ y, ‖fderiv ℝ v y‖ ≤ C) (θ : 𝓢(Space, Space)) (W : Space →L[ℝ] Space) :
    Integrable (fun y => inner ℝ (v y) (θ y)) ∧
    Integrable (fun y => inner ℝ (fderiv ℝ v y (W y)) (θ y)) ∧
    Integrable (fun y => inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y)) ∧
    ∫ y, inner ℝ (fderiv ℝ v y (W y)) (θ y) = -∫ y, inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y) := by
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  have hDc : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ v y (unitVector j)) := fun j =>
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDb : ∀ (j : Fin 3) y, ‖fderiv ℝ v y (unitVector j)‖ ≤ C := fun j y => by
    calc ‖fderiv ℝ v y (unitVector j)‖ ≤ ‖fderiv ℝ v y‖ * ‖unitVector j‖ := (fderiv ℝ v y).le_opNorm _
      _ ≤ C := by
          rw [show ‖unitVector j‖ = 1 by simp [unitVector], mul_one]
          exact hC1 y
  set θk : Fin 3 → 𝓢(Space, Space) := fun j => SchwartzMap.smulLeftCLM Space (fun y : Space => (W y) j) θ
  have hθk : ∀ j y, θk j y = (W y) j • θ y := fun j y => by
    simp only [θk, SchwartzMap.smulLeftCLM_apply_apply (hasTG W j)]
  have P1 : ∀ y, inner ℝ (fderiv ℝ v y (W y)) (θ y) = ∑ j, inner ℝ (fderiv ℝ v y (unitVector j)) (θk j y) := by
    intro y
    rw [clm_decomp (fderiv ℝ v y) (W y), sum_inner]
    simp only [hθk, inner_smul_left, inner_smul_right]
    simp
  have P2 : ∀ y, inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y) =
      ∑ j, inner ℝ (v y) ((∂_{unitVector j} (θk j)) y) := by
    intro y
    simp only [θk, lineDeriv_coord_smul]
    rw [clm_decomp (fderiv ℝ θ y) (W y)]
    simp only [Internal.DriftSymbolWeakFreq.inner_unit, Finset.sum_smul, ← inner_sum, Finset.sum_add_distrib]
  have I1 : ∀ j, Integrable (fun y => inner ℝ (fderiv ℝ v y (unitVector j)) (θk j y)) := fun j =>
    integrable_inner_rapid (hDc j) (hDb j) (θk j)
  have I2 : ∀ j, Integrable (fun y => inner ℝ (v y) ((∂_{unitVector j} (θk j)) y)) := fun j =>
    integrable_inner_rapid hv.continuous hC0 _
  have W1 : ∀ j, ∫ y, inner ℝ (v y) ((∂_{unitVector j} (θk j)) y) =
      -∫ y, inner ℝ (fderiv ℝ v y (unitVector j)) (θk j y) := fun j => by
    have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (μ := volume) (B := innerSL ℝ) (v := unitVector j) (f := v) (g := ⇑(θk j)) (I1 j)
      (by
        refine (I2 j).congr (ae_of_all _ fun x => ?_)
        simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
        rfl)
      (integrable_inner_rapid hv.continuous hC0 (θk j)) (fun x _ => hvd x)
      (fun x _ => (θk j).differentiableAt)
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact key
  have eP1 : (fun y => inner ℝ (fderiv ℝ v y (W y)) (θ y)) =
      fun y => ∑ j, inner ℝ (fderiv ℝ v y (unitVector j)) (θk j y) := funext P1
  have eP2 : (fun y => inner ℝ (v y) (fderiv ℝ θ y (W y)
      + (∑ j : Fin 3, inner ℝ (W (unitVector j)) (unitVector j)) • θ y)) =
      fun y => ∑ j, inner ℝ (v y) ((∂_{unitVector j} (θk j)) y) := funext P2
  refine ⟨integrable_inner_rapid hv.continuous hC0 θ, ?_, ?_, ?_⟩
  · rw [eP1]
    exact integrable_finsetSum _ fun j _ => I1 j
  · rw [eP2]
    exact integrable_finsetSum _ fun j _ => I2 j
  · rw [eP1, eP2, integral_finsetSum _ fun j _ => I1 j, integral_finsetSum _ fun j _ => I2 j,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [W1, neg_neg]

open Breakdown.SteadyCert.Internal.DriftSymbolWeakTransport in
theorem drift_pair {v : Space → Space} (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC0 : ∀ y, ‖v y‖ ≤ C)
    (hC1 : ∀ y, ‖fderiv ℝ v y‖ ≤ C) (α a : ℝ) (χ : 𝓢(Space, Space)) :
    Integrable (fun y => inner ℝ (driftField α a v (fderiv ℝ v) y) (χ y)) ∧
    ∫ y, inner ℝ (driftField α a v (fderiv ℝ v) y) (χ y) =
      ∫ y, inner ℝ (v y) (transportAdjoint α a χ y) := by
  set g : ℝ := 1 / (2 * α) with hg
  obtain ⟨i1, i2, j2, e2⟩ := transport_pair hv hC0 hC1 χ (ContinuousLinearMap.id ℝ Space)
  obtain ⟨-, i3, j3, e3⟩ := transport_pair hv hC0 hC1 χ axialL
  obtain ⟨i4, -, -, -⟩ := transport_pair hv hC0 hC1 (SchwartzMap.postcompCLM (𝕜 := ℝ) axialL χ) axialL
  simp only [ContinuousLinearMap.id_apply, axialL_apply, SchwartzMap.postcompCLM_apply] at i2 j2 e2 i3 j3 e3 i4
  have d1 : (∑ j : Fin 3, inner ℝ (unitVector j) (unitVector j)) = (3 : ℝ) := by
    simp [unitVector]
  have d2 : (∑ j : Fin 3, inner ℝ (axialTurn (unitVector j)) (unitVector j)) = (0 : ℝ) := by
    simp [unitVector, axialTurn, Fin.sum_univ_three, PiLp.inner_apply]
  rw [d1] at j2 e2
  rw [d2] at j3 e3
  simp only [zero_smul, add_zero] at j3 e3
  have hL : (fun y => inner ℝ (driftField α a v (fderiv ℝ v) y) (χ y)) = fun y =>
      ((1 - g) * inner ℝ (v y) (χ y) + g * inner ℝ (fderiv ℝ v y y) (χ y))
        + (a * inner ℝ (fderiv ℝ v y (axialTurn y)) (χ y) + a * inner ℝ (v y) (axialTurn (χ y))) := by
    funext y
    simp only [driftField, inner_add_left, inner_sub_left, inner_smul_left, inner_axialTurn]
    simp
    ring
  have hR : (fun y => inner ℝ (v y) (transportAdjoint α a χ y)) = fun y =>
      ((1 - g) * inner ℝ (v y) (χ y) + (-g) * inner ℝ (v y) (fderiv ℝ χ y y + (3 : ℝ) • χ y))
        + ((-a) * inner ℝ (v y) (fderiv ℝ χ y (axialTurn y)) + a * inner ℝ (v y) (axialTurn (χ y))) := by
    funext y
    simp only [transportAdjoint, inner_add_right, inner_sub_right, inner_smul_right]
    ring
  have A1 : Integrable (fun y => (1 - g) * inner ℝ (v y) (χ y)) := i1.const_mul _
  have A2 : Integrable (fun y => g * inner ℝ (fderiv ℝ v y y) (χ y)) := i2.const_mul _
  have A3 : Integrable (fun y => a * inner ℝ (fderiv ℝ v y (axialTurn y)) (χ y)) := i3.const_mul _
  have A4 : Integrable (fun y => a * inner ℝ (v y) (axialTurn (χ y))) := i4.const_mul _
  have B2 : Integrable (fun y => (-g) * inner ℝ (v y) (fderiv ℝ χ y y + (3 : ℝ) • χ y)) := j2.const_mul _
  have B3 : Integrable (fun y => (-a) * inner ℝ (v y) (fderiv ℝ χ y (axialTurn y))) := j3.const_mul _
  have S1 : Integrable (fun y => (1 - g) * inner ℝ (v y) (χ y) + g * inner ℝ (fderiv ℝ v y y) (χ y)) :=
    A1.add A2
  have S2 : Integrable (fun y => a * inner ℝ (fderiv ℝ v y (axialTurn y)) (χ y)
      + a * inner ℝ (v y) (axialTurn (χ y))) := A3.add A4
  have S3 : Integrable (fun y => (1 - g) * inner ℝ (v y) (χ y)
      + (-g) * inner ℝ (v y) (fderiv ℝ χ y y + (3 : ℝ) • χ y)) := A1.add B2
  have S4 : Integrable (fun y => (-a) * inner ℝ (v y) (fderiv ℝ χ y (axialTurn y))
      + a * inner ℝ (v y) (axialTurn (χ y))) := B3.add A4
  refine ⟨by rw [hL]; exact S1.add S2, ?_⟩
  rw [hL, hR, integral_add S1 S2, integral_add S3 S4,
    integral_add A1 A2, integral_add A3 A4, integral_add A1 B2, integral_add B3 A4,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, e2, e3]
  ring

theorem exists_coeff {q : Space → CSpace} (hs : ContDiff ℝ ∞ q) {r : ℝ} (hr : 0 < r)
    (h0 : ∀ ξ, ‖ξ‖ < r → q ξ = 0) (hc : ∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ) :
    ∃ c : Space → ℂ, Differentiable ℝ c ∧ ∀ ξ, q ξ = c ξ • freqVec ξ := by
  obtain ⟨c, hc⟩ := hc
  refine ⟨fun ξ => ((‖ξ‖ ^ 2)⁻¹ : ℝ) • inner ℂ (freqVec ξ) (q ξ), ?_, ?_⟩
  · intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hr] with x hx
      rw [h0 x (by simpa using hx)]
      simp
    · have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hξ)
      have d1 : DifferentiableAt ℝ (fun x : Space => ‖x‖ ^ 2) ξ :=
        differentiableAt_id.norm_sq ℝ
      have d2 : DifferentiableAt ℝ (fun x : Space => inner ℂ (freqVec x) (q x)) ξ :=
        (complexifyVec.differentiableAt).inner ℂ ((hs.differentiable (by simp)) ξ)
      exact (d1.inv hn).smul d2
  · intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      rw [h0 0 (by simpa using hr)]
      simp [freqVec]
    · have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hξ
      beta_reduce
      rw [hc ξ, inner_smul_right, inner_self_eq_norm_sq_to_K, Breakdown.SmoothFlow.Internal.norm_freqVec]
      congr 1
      rw [Complex.real_smul]
      push_cast
      field_simp
      rfl

theorem flowAdjoint_long {q : Space → CSpace} {c : Space → ℂ} (hc : Differentiable ℝ c)
    (hq : ∀ ξ, q ξ = c ξ • freqVec ξ) (α a : ℝ) (ξ : Space) :
    ∃ d : ℂ, flowAdjoint α a q ξ = d • freqVec ξ := by
  have hqf : q = fun x => c x • freqVec x := funext hq
  have hd : ∀ w, fderiv ℝ q ξ w = c ξ • freqVec w + fderiv ℝ c ξ w • freqVec ξ := by
    intro w
    have h := (hc ξ).hasFDerivAt.smul complexifyVec.hasFDerivAt
    rw [hqf]
    simp only [freqVec]
    rw [show (fun x => c x • complexifyVec x) = c • ⇑complexifyVec from rfl, h.fderiv]
    simp
  refine ⟨((1 - 1 / (2 * α) : ℝ) : ℂ) * c ξ + ((1 / (2 * α) : ℝ) : ℂ) * (c ξ + fderiv ℝ c ξ ξ)
      - (a : ℂ) * fderiv ℝ c ξ (axialTurn ξ), ?_⟩
  simp only [flowAdjoint, hd, hq]
  ext i
  fin_cases i <;> simp [freqTurn, axialTurn, freqVec, complexifyVec] <;> ring

theorem flowAdjoint_conjSym {q : Space → CSpace} (hs : Differentiable ℝ q)
    (hh : ∀ ξ, q (-ξ) = conjVec (q ξ)) (α a : ℝ) (ξ : Space) :
    flowAdjoint α a q (-ξ) = conjVec (flowAdjoint α a q ξ) := by
  have hd : ∀ w, fderiv ℝ q (-ξ) w = -conjVec (fderiv ℝ q ξ w) := by
    intro w
    have e : (fun x => q (-x)) = fun x => conjVec (q x) := funext hh
    have h1 : HasFDerivAt (fun x => q (-x)) ((fderiv ℝ q (-ξ)).comp (-ContinuousLinearMap.id ℝ Space)) ξ :=
      (hs (-ξ)).hasFDerivAt.comp ξ (hasFDerivAt_id ξ).neg
    have h2 : HasFDerivAt (fun x => conjVec (q x)) (conjVec.comp (fderiv ℝ q ξ)) ξ :=
      conjVec.hasFDerivAt.comp ξ (hs ξ).hasFDerivAt
    rw [e] at h1
    have := congrArg (fun L : Space →L[ℝ] CSpace => L (-w)) (h1.unique h2)
    simpa using this
  have ht : axialTurn (-ξ) = -axialTurn ξ := by
    ext i
    fin_cases i <;> simp [axialTurn]
  have hf : ∀ z, freqTurn (conjVec z) = conjVec (freqTurn z) := by
    intro z
    ext i
    fin_cases i <;> simp [freqTurn, conjVec]
  simp only [flowAdjoint, hh, hd, ht, map_neg, hf, map_add, map_sub, map_smul, neg_neg]

theorem complexifyVec_apply (ξ : Space) (i : Fin 3) : complexifyVec ξ i = ((ξ i : ℝ) : ℂ) := rfl

end Internal.ResidualGradient

open Breakdown.FracCert.Internal.ResidualGradient WeakRegularInternal Breakdown.SteadyCert.Internal.DriftSymbolWeak
  Breakdown.Freq.Internal.NicePairing in
theorem residualGradient (h1 : SymbolL1OfMomentsStatement) (h2 : FieldSmoothOfMomentsStatement) :
    ResidualGradientStatement := by
  intro α hα hα2 a U hM q hh hsm hcs hr0 hcx
  obtain ⟨r, hr, h0⟩ := hr0
  obtain ⟨c, hcd, hqc⟩ := exists_coeff hsm hr h0 hcx
  have hwm := (h1 U hM).1
  obtain ⟨s, hsd⟩ : ∃ s, s = cleanSymbol (symbolX U) := ⟨_, rfl⟩
  have hs : ∀ k, MemLp s 1 (weightL1Measure k) := fun k => by rw [hsd]; exact memLp_clean U hwm k
  have hsol : IsSolenoidalSymbol s := fun ξ => by
    rw [hsd]; exact ⟨cleanSymbol_div _ ξ, cleanSymbol_conjSym _ ξ⟩
  have hsi : Integrable s := Breakdown.SmoothFlow.Internal.integrable_of_weight (hs 0)
  have hsm3 : Integrable (fun ξ => (1 + ‖ξ‖) ^ 3 * ‖s ξ‖) := by rw [hsd]; exact moments_clean U hwm 3
  obtain ⟨hV, hB⟩ := h2 _ (moments_clean U hwm) (cleanSymbol_conjSym _)
  rw [← hsd] at hV hB
  have hVs : physField (symbolX U) = physField s := by rw [hsd, physField_clean]
  obtain ⟨C0, hC0⟩ := hB 0
  obtain ⟨C1, hC1⟩ := hB 1
  have hb0 : ∀ y, ‖physField s y‖ ≤ max C0 C1 := fun y => by
    have h := hC0 y
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (le_max_left _ _)
  have hb1 : ∀ y, ‖fderiv ℝ (physField s) y‖ ≤ max C0 C1 := fun y => by
    have h := hC1 y
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (le_max_right _ _)
  obtain ⟨Q, hQ⟩ := exists_rapid hcs hsm
  have hQf : ⇑Q = q := funext hQ
  have hQh : ∀ ξ, Q (-ξ) = conjVec (Q ξ) := fun ξ => by rw [hQ, hQ, hh]
  obtain ⟨χ, hχ⟩ : ∃ χ : 𝓢(Space, Space), ∀ y, χ y = realVec ((𝓕⁻ Q) y) :=
    ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) realVec (𝓕⁻ Q), fun y => by simp [SchwartzMap.postcompCLM_apply]⟩
  have hqχ : physField q = ⇑χ := by
    rw [physField_of_rapid Q hQf]
    funext y
    rw [hχ]
  have hΦc : HasCompactSupport (flowAdjoint α a q) := hcs.mono' (support_flowAdjoint_subset α a q)
  obtain ⟨Φ, hΦ⟩ := exists_rapid hΦc (contDiff_flowAdjoint hsm)
  have hΦh : ∀ ξ, Φ (-ξ) = conjVec (Φ ξ) := fun ξ => by
    rw [hΦ, hΦ]
    exact flowAdjoint_conjSym (hsm.differentiable (by simp)) hh α a ξ
  have hTA : ∀ y, transportAdjoint α a χ y = realVec ((𝓕⁻ Φ) y) := by
    intro y
    have h := flowAdjointInverse α a Q Φ (fun ξ => by rw [hΦ, hQf]) y
    have e : (fun x => realVec ((𝓕⁻ Q) x)) = ⇑χ := funext fun x => (hχ x).symm
    rw [h, e]
  have hP : profilePressure U = physScalar (pressureSymbol s) := by
    rw [profilePressure, hsd, pressure_clean U]
  have hps : ∀ k, MemLp (fun ξ => pressureSymbol s ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) 1
      (weightL1Measure k) := memLp_pressureSymbol_single hs hsol
  have hpn : ∀ ξ, ‖pressureSymbol s ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ = ‖pressureSymbol s ξ‖ :=
    fun ξ => by simp [norm_smul]
  have hpi : Integrable (pressureSymbol s) := by
    have h := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).integrable_comp
      (Breakdown.SmoothFlow.Internal.integrable_of_weight (hps 0))
    simpa using h
  have hpv : Integrable (fun ξ => pressureSymbol s ξ • freqVec ξ) := by
    refine (Breakdown.SmoothFlow.Internal.integrable_pow_mul_of_weight (hps 1) le_rfl).mono'
      (hpi.aestronglyMeasurable.smul complexifyVec.continuous.aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
    rw [norm_smul, Breakdown.SmoothFlow.Internal.norm_freqVec, hpn, pow_one]
    exact (mul_comm _ _).le
  obtain ⟨gp, hgpd⟩ : ∃ gp : Space → CSpace,
      gp = fun ξ => (2 * (π : ℂ) * Complex.I * pressureSymbol s ξ) • freqVec ξ := ⟨_, rfl⟩
  have hgpi : Integrable gp := by
    rw [hgpd]
    exact (hpv.smul (2 * (π : ℂ) * Complex.I)).congr
      (ae_of_all _ fun ξ => by simp only [Pi.smul_apply, smul_smul])
  have hpow : Integrable (powerSymbol α s) :=
    integrable_powerSymbol (by linarith) (by linarith) hsi.aestronglyMeasurable hsm3
  have hadv : Integrable (advectionSymbol s) :=
    Breakdown.SmoothFlow.Internal.integrable_of_weight (memLp_advectionSymbol hs 0)
  obtain ⟨H, hHd⟩ : ∃ H : Space → CSpace,
      H = fun ξ => powerSymbol α s ξ + (advectionSymbol s ξ + gp ξ) := ⟨_, rfl⟩
  have hHi : Integrable H := by
    rw [hHd]
    exact hpow.add (hadv.add hgpi)
  have hF : ∀ y, fractionalPowerAt α (physField s) y = physField (powerSymbol α s) y := fun y =>
    powerPhysPower_of α hα (by linarith)
      (Periodic.planeWaveEigen_of α hα (by linarith) (symbolScalar normalizer) normalizer) _ (hs 3) y
  have hA : ∀ y, advectionAt (physField s) y = physField (advectionSymbol s) y :=
    advectionAt_physField hs hsol
  have hG : ∀ y, gradientAt (profilePressure U) y = physField gp y := fun y => by
    rw [hP, hgpd]
    exact gradientAt_physScalar hpi hpv y
  have hHeq : ∀ y, fractionalPowerAt α (physField s) y + advectionAt (physField s) y
      + gradientAt (profilePressure U) y = physField H y := fun y => by
    rw [hF, hA, hG, hHd, physField_add (f := powerSymbol α s) (g := fun ξ => advectionSymbol s ξ + gp ξ) hpow
      (hadv.add hgpi) y, physField_add hadv hgpi y, add_assoc]
  have hHdiv : ∀ ξ, ∑ i, ((ξ i : ℝ) : ℂ) * H ξ i = 0 := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp
    have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hξ)
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hsq : ∑ i, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
      have hr2 : ‖ξ‖ ^ 2 = ∑ i, ξ i * ξ i := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs, sq]
      rw [hr2]
      push_cast
      rfl
    have eP : ∑ i, ((ξ i : ℝ) : ℂ) * powerSymbol α s ξ i =
        (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * s ξ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [powerSymbol, PiLp.smul_apply, smul_eq_mul]
      ring
    have eG : ∑ i, ((ξ i : ℝ) : ℂ) * gp ξ i =
        (2 * (π : ℂ) * Complex.I * pressureSymbol s ξ) * ∑ i, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hgpd, PiLp.smul_apply, smul_eq_mul, freqVec, complexifyVec_apply]
      ring
    rw [hHd]
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
    rw [eP, eG, hsq, (hsol ξ).1, pressureSymbol]
    field_simp
    ring
  have hres : ∀ y, profileResidual α a U y =
      driftField α a (physField s) (fderiv ℝ (physField s)) y + physField H y := by
    intro y
    rw [← hHeq y]
    simp only [profileResidual, rotatingProfileResidual, driftField, one_smul]
    rw [hVs]
    abel
  rw [hqχ]
  have hsplit : (fun y => inner ℝ (profileResidual α a U y) (χ y)) = fun y =>
      inner ℝ (driftField α a (physField s) (fderiv ℝ (physField s)) y) (χ y)
        + inner ℝ (physField H y) (χ y) := funext fun y => by rw [hres, inner_add_left]
  obtain ⟨hDi, hDe⟩ := drift_pair hV hb0 hb1 α a χ
  have hHc : Continuous (physField H) := continuous_physField_of hHi
  have hHb : ∀ y, ‖physField H y‖ ≤ ∫ ξ, ‖H ξ‖ := fun y => (norm_realVec_le' _).trans
    (VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (-innerₗ Space) H y)
  have hHi2 := integrable_inner_rapid hHc hHb χ
  rw [hsplit, integral_add hDi hHi2, hDe]
  have e1 : ∫ y, inner ℝ (physField s y) (transportAdjoint α a χ y) = 0 := by
    simp_rw [hTA]
    rw [pair_symbol hsi Φ hΦh]
    have hz : (fun ξ => inner ℝ (s ξ) (Φ ξ)) = fun _ => (0 : ℝ) := by
      funext ξ
      obtain ⟨d, hd⟩ := flowAdjoint_long hcd hqc α a ξ
      rw [hΦ, hd]
      exact inner_freqVec_zero (hsol ξ).1 d
    rw [hz, integral_zero]
  have e2 : ∫ y, inner ℝ (physField H y) (χ y) = 0 := by
    simp_rw [hχ]
    rw [pair_symbol hHi Q hQh]
    have hz : (fun ξ => inner ℝ (H ξ) (Q ξ)) = fun _ => (0 : ℝ) := by
      funext ξ
      rw [hQ, hqc ξ]
      exact inner_freqVec_zero (hHdiv ξ) (c ξ)
    rw [hz, integral_zero]
  rw [e1, e2, add_zero]

end Breakdown.FracCert
