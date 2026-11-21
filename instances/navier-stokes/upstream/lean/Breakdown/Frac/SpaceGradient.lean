import Breakdown.Frac.StSpace
import Breakdown.FreqTr.EmbedNegSsp

open scoped ContDiff ENNReal SchwartzMap FourierTransform
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal.SpaceGradient

open LineDeriv FourierTransform SchwartzMap Freq Freq.Internal.EmbedNegSsp

theorem norm_cvec (v : Space) : ‖complexifyVec v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [complexifyVec]

theorem inner_cvec (a b : Space) :
    inner ℂ (complexifyVec a) (complexifyVec b) = ((inner ℝ a b : ℝ) : ℂ) := by
  simp [complexifyVec, PiLp.inner_apply, mul_comm]

def complexTest {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    𝓢(Space, CSpace) :=
  HasCompactSupport.toSchwartzMap (f := fun x => complexifyVec (u x))
    (hc.comp_left (map_zero complexifyVec)) (complexifyVec.contDiff.comp hu)

theorem coe_complexTest {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ⇑(complexTest hu hc) = fun x => complexifyVec (u x) := rfl

theorem integrable_norm_sq (S : 𝓢(Space, CSpace)) : Integrable (fun x => ‖S x‖ ^ 2) := by
  have h : MemLp S ((2 : ℕ) : ENNReal) volume := by simpa using S.memLp 2
  exact h.integrable_norm_pow two_ne_zero

theorem sum_sq_coord (ξ : Space) : ∑ k : Fin 3, (ξ k) ^ 2 = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_sq_transform_pd (S : 𝓢(Space, CSpace)) (k : Fin 3) (ξ : Space) :
    ‖𝓕 (∂_{unitVector k} S) ξ‖ ^ 2 = (2 * π) ^ 2 * (ξ k) ^ 2 * ‖𝓕 S ξ‖ ^ 2 := by
  rw [freqTr_pd_apply, norm_smul, mul_pow]
  congr 1
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [mul_one, mul_pow, mul_pow, sq_abs]

theorem integral_grad_eq {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∫ y, ∑ i : Fin 3, ‖fderiv ℝ u y (unitVector i)‖ ^ 2 =
      ∫ ξ, (2 * π * ‖ξ‖) ^ 2 * ‖𝓕 (complexTest hu hc) ξ‖ ^ 2 := by
  have e : ∀ y, ∑ i : Fin 3, ‖fderiv ℝ u y (unitVector i)‖ ^ 2 =
      ∑ i : Fin 3, ‖(∂_{unitVector i} (complexTest hu hc) : 𝓢(Space, CSpace)) y‖ ^ 2 := by
    intro y
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_lineDeriv_eq (differentiable_of_smooth hu) (coe_complexTest hu hc) i, norm_cvec]
    rfl
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_norm_sq _]
  rw [Finset.sum_congr rfl fun i _ => (integral_norm_sq_fourier _).symm]
  rw [← integral_finsetSum _ fun i _ => integrable_norm_sq _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [Finset.sum_congr rfl fun k _ => norm_sq_transform_pd _ k ξ, ← Finset.sum_mul,
    ← Finset.mul_sum, sum_sq_coord]
  ring

theorem integral_norm_eq {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∫ y, ‖u y‖ ^ 2 = ∫ ξ, ‖𝓕 (complexTest hu hc) ξ‖ ^ 2 := by
  rw [integral_norm_sq_fourier, coe_complexTest]
  simp only [norm_cvec]

theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  rw [ae_iff]
  simp

theorem rpow_le_cube {k α : ℝ} (hk : 0 ≤ k) (hα : 1 < α) (hα2 : α < 3 / 2) :
    k ^ (2 * α) ≤ 1 + k ^ 3 := by
  rcases le_total k 1 with h | h
  · have := Real.rpow_le_one hk h (by linarith : (0 : ℝ) ≤ 2 * α)
    have : 0 ≤ k ^ 3 := by positivity
    linarith
  · have h3 : k ^ (2 * α) ≤ k ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (by push_cast; linarith)
    rw [Real.rpow_natCast] at h3
    linarith

theorem sq_le_rpow {k α : ℝ} (hk : 0 ≤ k) (hα : 1 < α) :
    k ^ 2 ≤ 1 + k ^ (2 * α) := by
  rcases le_total k 1 with h | h
  · have := pow_le_one₀ (n := 2) hk h
    have : 0 ≤ k ^ (2 * α) := Real.rpow_nonneg hk _
    linarith
  · have h3 : k ^ ((2 : ℕ) : ℝ) ≤ k ^ (2 * α) :=
      Real.rpow_le_rpow_of_exponent_le h (by push_cast; linarith)
    rw [Real.rpow_natCast] at h3
    linarith

theorem sesq_swap (g : Space → CSpace) (hg : Integrable g) (S : 𝓢(Space, CSpace)) :
    ∫ ξ, inner ℂ (𝓕 g ξ) ((𝓕 S : 𝓢(Space, CSpace)) ξ) = ∫ x, inner ℂ (g x) (S x) := by
  set F : 𝓢(Space, CSpace) := 𝓕 S with hF
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L := innerₗ Space) (μ := volume) (ν := volume) continuous_fourierChar continuous_inner hg
    F.integrable
  have e : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (-(innerₗ Space).flip) (⇑F) x =
      S x := by
    intro x
    have h2 : 𝓕⁻ (⇑F) x = S x := by
      rw [← SchwartzMap.fourierInv_coe, hF, FourierTransform.fourierInv_fourier_eq]
    rw [← h2, Real.fourierInv_eq]
    simp [VectorFourier.fourierIntegral, real_inner_comm]
  simp only [innerSL_apply_apply, e] at h
  exact h

theorem transform_undef (g : Space → CSpace) (hg : ¬ Integrable g) (ξ : Space) : 𝓕 g ξ = 0 := by
  rw [Real.fourier_eq]
  exact integral_undef (mt (Real.fourierIntegral_convergent_iff ξ).1 hg)

theorem symbol_apply (h1 : SymbolStatement) {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2)
    {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (ξ : Space) :
    𝓕 (fun x => complexifyVec (fractionalPowerAt α u x)) ξ =
      (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) • (𝓕 (complexTest hu hc) : 𝓢(Space, CSpace)) ξ := by
  rw [SchwartzMap.fourier_coe, coe_complexTest]
  exact h1 α hα hα2 (hc.toSchwartzMap hu) ξ

theorem pairing_eq (h1 : SymbolStatement) {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2)
    {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∫ x, inner ℝ (u x) (fractionalPowerAt α u x) =
      ∫ ξ, (2 * π * ‖ξ‖) ^ (2 * α) * ‖(𝓕 (complexTest hu hc) : 𝓢(Space, CSpace)) ξ‖ ^ 2 := by
  set g : Space → CSpace := fun x => complexifyVec (fractionalPowerAt α u x) with hg
  set F : 𝓢(Space, CSpace) := 𝓕 (complexTest hu hc) with hF
  have hs : ∀ ξ, 𝓕 g ξ = (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) • F ξ :=
    symbol_apply h1 hα hα2 hu hc
  by_cases hint : Integrable g
  · have h := sesq_swap g hint (complexTest hu hc)
    rw [← hF] at h
    simp_rw [hs] at h
    have lhs : ∀ ξ, inner ℂ ((((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) • F ξ) (F ξ) =
        (((2 * π * ‖ξ‖) ^ (2 * α) * ‖F ξ‖ ^ 2 : ℝ) : ℂ) := by
      intro ξ
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal]
      push_cast
      rfl
    have rhs : ∀ x, inner ℂ (g x) (complexTest hu hc x) =
        ((inner ℝ (u x) (fractionalPowerAt α u x) : ℝ) : ℂ) := by
      intro x
      rw [coe_complexTest]
      simp only [hg]
      rw [inner_cvec, real_inner_comm]
    simp_rw [lhs, rhs, integral_complex_ofReal] at h
    exact (Complex.ofReal_injective h).symm
  · have h0 : ∀ ξ, ξ ≠ 0 → F ξ = 0 := by
      intro ξ hξ
      have e := hs ξ
      rw [transform_undef g hint ξ] at e
      have hm : (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) ≠ 0 := by
        have hp : 0 < 2 * π * ‖ξ‖ := by
          have := norm_pos_iff.2 hξ
          positivity
        exact_mod_cast (Real.rpow_pos_of_pos hp _).ne'
      exact (smul_eq_zero.1 e.symm).resolve_left hm
    have hae : (⇑F) =ᵐ[volume] 0 := by
      filter_upwards [ae_ne_zero] with ξ hξ using h0 ξ hξ
    have hu0 : ∀ x, u x = 0 := by
      intro x
      have h2 : complexTest hu hc x = 0 := by
        have e : complexTest hu hc x = 𝓕⁻ (⇑F) x := by
          rw [← SchwartzMap.fourierInv_coe, hF, FourierTransform.fourierInv_fourier_eq]
        rw [e, fourierInv_congr_ae hae]
        simp [Real.fourierInv_eq]
      rw [coe_complexTest] at h2
      simp only at h2
      have e := norm_cvec (u x)
      rw [h2, norm_zero] at e
      exact norm_eq_zero.1 e.symm
    have l : ∫ x, inner ℝ (u x) (fractionalPowerAt α u x) = 0 := by simp [hu0]
    rw [l, integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · filter_upwards [hae] with ξ hξ
      simp [hξ]

theorem integrable_weight {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) (F : 𝓢(Space, CSpace)) :
    Integrable (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α) * ‖F ξ‖ ^ 2) := by
  set C := ‖F.toBoundedContinuousFunction‖
  have hb : ∀ ξ, ‖F ξ‖ ≤ C := fun ξ => by
    simpa using F.toBoundedContinuousFunction.norm_coe_le_norm ξ
  have i1 : Integrable (fun ξ => ‖F ξ‖) := F.integrable.norm
  have i3 : Integrable (fun ξ : Space => ‖ξ‖ ^ 3 * ‖F ξ‖) := SchwartzMap.integrable_pow_mul volume F 3
  have hcont : Continuous (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α) * ‖F ξ‖ ^ 2) := by
    have h1 : Continuous (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α)) :=
      (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr (by linarith))
    exact h1.mul (F.continuous.norm.pow 2)
  refine Integrable.mono' ((i1.const_mul C).add ((i3.const_mul ((2 * π) ^ 3)).const_mul C))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  have hk := rpow_le_cube (k := 2 * π * ‖ξ‖) (by positivity) hα hα2
  have a := norm_nonneg (F ξ)
  have hbξ := hb ξ
  rw [Real.norm_of_nonneg (by positivity)]
  have hF2 : ‖F ξ‖ ^ 2 ≤ C * ‖F ξ‖ := by nlinarith
  have hC : 0 ≤ C := a.trans hbξ
  calc (2 * π * ‖ξ‖) ^ (2 * α) * ‖F ξ‖ ^ 2 ≤ (1 + (2 * π * ‖ξ‖) ^ 3) * (C * ‖F ξ‖) :=
        mul_le_mul hk hF2 (by positivity) (by positivity)
    _ = C * ‖F ξ‖ + C * ((2 * π) ^ 3 * (‖ξ‖ ^ 3 * ‖F ξ‖)) := by ring

end FracInternal.SpaceGradient

open FracInternal.SpaceGradient in
theorem fracGradientBound_of (h1 : SymbolStatement) : FracGradientBoundStatement := by
  intro α hα hα2 W hW hc
  rw [pairing_eq h1 hα hα2 hW hc, integral_grad_eq hW hc, integral_norm_eq hW hc]
  set F : 𝓢(Space, Freq.CSpace) := 𝓕 (complexTest hW hc)
  refine ⟨integral_nonneg fun ξ => by positivity, ?_⟩
  have iw := integrable_weight hα hα2 F
  rw [← integral_add (integrable_norm_sq F) iw]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity)
    ((integrable_norm_sq F).add iw) (Filter.Eventually.of_forall fun ξ => ?_)
  have hk := sq_le_rpow (k := 2 * π * ‖ξ‖) (by positivity) hα
  have a : 0 ≤ ‖F ξ‖ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hk a
  simp only
  linarith

end Breakdown
