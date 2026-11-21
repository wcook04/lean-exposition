import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology ComplexConjugate
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def varConstMap (a : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace) (t : ℝ) (ξ : Space) : CSpace :=
  ((heatSymbol (t - a) ξ : ℝ) : ℂ) • F₀ ξ +
    ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (G s) ξ

theorem varConstMap_self (a : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace) :
    varConstMap a F₀ G a = F₀ := by
  funext ξ
  simp [varConstMap, heatSymbol]

private theorem convC_congr_ae {p p' q q' : Space → ℂ} (hp : p =ᵐ[volume] p') (hq : q =ᵐ[volume] q')
    (ξ : Space) : convC p q ξ = convC p' q' ξ := by
  unfold convC
  refine integral_congr_ae ?_
  have hq' : ∀ᵐ η ∂(volume : Measure Space), q (ξ - η) = q' (ξ - η) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ).ae hq
  filter_upwards [hp, hq'] with η h1 h2
  rw [h1, h2]

theorem nonlinSymbol_congr_ae {f g : Space → CSpace} (h : f =ᵐ[volume] g) :
    nonlinSymbol f = nonlinSymbol g := by
  have hA : advectionSymbol f = advectionSymbol g := by
    funext ξ
    unfold advectionSymbol advectionBilin
    congr 1
    funext i
    refine Finset.sum_congr rfl fun j _ => convC_congr_ae ?_ ?_ ξ
    · filter_upwards [h] with η hη
      rw [hη]
    · filter_upwards [h] with η hη
      rw [hη]
  funext ξ
  simp only [nonlinSymbol, hA]

theorem isHsCurve_congr {m : ℕ} {F G : ℝ → Space → CSpace} {a b : ℝ}
    (hG : IsHsCurve m G a b) (h : ∀ t ∈ Icc a b, F t =ᵐ[volume] G t) :
    IsHsCurve m F a b := by
  obtain ⟨h1, h2⟩ := hG
  refine ⟨fun t ht => ?_, fun t₀ ht₀ => ?_⟩
  · obtain ⟨hm, hs⟩ := h1 t ht
    refine ⟨hm.congr (h t ht).symm, ?_⟩
    have hEq : hsNormSq m (F t) = hsNormSq m (G t) := by
      unfold hsNormSq
      refine lintegral_congr_ae ?_
      filter_upwards [h t ht] with ξ hξ
      rw [hξ]
    rw [hEq]
    exact hs
  · refine Tendsto.congr' ?_ (h2 t₀ ht₀)
    filter_upwards [self_mem_nhdsWithin] with t ht
    unfold hsNormSq
    refine lintegral_congr_ae ?_
    filter_upwards [h t ht, h t₀ ht₀] with ξ e1 e2
    simp [Pi.sub_apply, e1, e2]

private theorem sum_sq_eq_norm_sq (ξ : Space) : ∑ i, (ξ i) ^ 2 = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

private theorem dot_divFreeC (ξ : Space) (z : CSpace) :
    ∑ i, ((ξ i : ℝ) : ℂ) * divFreeC ξ z i = 0 := by
  have hf : ∀ i, freqVec ξ i = ((ξ i : ℝ) : ℂ) := fun i => rfl
  have hl : ∀ i, divFreeC ξ z i = z i -
      (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (∑ k, ((ξ k : ℝ) : ℂ) * z k) * ((ξ i : ℝ) : ℂ) := by
    intro i
    simp [divFreeC, hf]
  simp only [hl]
  have hs : ∑ i, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) = (((‖ξ‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← sum_sq_eq_norm_sq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => by ring
  by_cases h0 : ξ = 0
  · simp [h0]
  have hn : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hexp : ∑ i, ((ξ i : ℝ) : ℂ) * (z i -
      (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (∑ k, ((ξ k : ℝ) : ℂ) * z k) * ((ξ i : ℝ) : ℂ)) =
      (∑ k, ((ξ k : ℝ) : ℂ) * z k) - (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (∑ k, ((ξ k : ℝ) : ℂ) * z k) *
        ∑ i, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) := by
    generalize hS : (∑ k, ((ξ k : ℝ) : ℂ) * z k) = S
    generalize ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) = c
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, hs]
  have hc : (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (((‖ξ‖ ^ 2 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]
  linear_combination (-(∑ k, ((ξ k : ℝ) : ℂ) * z k)) * hc

theorem nonlinSymbol_div (f : Space → CSpace) (ξ : Space) :
    ∑ i, ((ξ i : ℝ) : ℂ) * nonlinSymbol f ξ i = 0 := by
  have h := dot_divFreeC ξ (advectionSymbol f ξ)
  simp only [nonlinSymbol]
  simp only [PiLp.neg_apply, mul_neg, Finset.sum_neg_distrib, h, neg_zero]

private theorem conjVec_apply (z : CSpace) (i : Fin 3) : conjVec z i = star (z i) := rfl

private theorem freqVec_apply (ξ : Space) (i : Fin 3) : freqVec ξ i = ((ξ i : ℝ) : ℂ) := rfl

private def conjVecIso : CSpace →ₗᵢ[ℝ] CSpace where
  toLinearMap := conjVec.toLinearMap
  norm_map' z := by
    simp only [ContinuousLinearMap.coe_coe, EuclideanSpace.norm_eq, conjVec_apply, norm_star]

private theorem convC_neg {u v u' v' : Space → ℂ} (hu : ∀ᵐ η ∂volume, u (-η) = star (u' η))
    (hv : ∀ᵐ η ∂volume, v (-η) = star (v' η)) (ξ : Space) :
    convC u v (-ξ) = star (convC u' v' ξ) := by
  unfold convC
  rw [← integral_neg_eq_self]
  have hv' : ∀ᵐ η ∂(volume : Measure Space), v (-(ξ - η)) = star (v' (ξ - η)) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ).ae hv
  refine (integral_congr_ae ?_).trans integral_conj
  filter_upwards [hu, hv'] with η h1 h2
  have : -ξ - -η = -(ξ - η) := by abel
  rw [this, h1, h2]
  simp

private theorem advectionBilin_neg {f : Space → CSpace} (h : ∀ᵐ η ∂volume, f (-η) = conjVec (f η))
    (ξ : Space) : advectionBilin f f (-ξ) = conjVec (advectionBilin f f ξ) := by
  ext i
  simp only [advectionBilin, conjVec_apply, PiLp.toLp_apply, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine convC_neg ?_ ?_ ξ
  · filter_upwards [h] with η hη
    rw [hη, conjVec_apply]
  · filter_upwards [h] with η hη
    rw [hη, conjVec_apply]
    simp [Complex.conj_ofReal]

private theorem divFreeC_neg_conj (ξ : Space) (z : CSpace) :
    divFreeC (-ξ) (conjVec z) = conjVec (divFreeC ξ z) := by
  ext i
  simp only [divFreeC, conjVec_apply, freqVec_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    norm_neg, star_sub, star_mul', star_sum, PiLp.neg_apply]
  simp [Complex.conj_ofReal, Finset.sum_neg_distrib]

theorem nonlinSymbol_neg {f : Space → CSpace} (h : ∀ᵐ η ∂volume, f (-η) = conjVec (f η)) (ξ : Space) :
    nonlinSymbol f (-ξ) = conjVec (nonlinSymbol f ξ) := by
  simp only [nonlinSymbol, advectionSymbol, advectionBilin_neg h, divFreeC_neg_conj, map_neg]

private theorem inner_freqVec (ξ : Space) (w : CSpace) :
    inner ℂ (freqVec ξ) w = ∑ i, ((ξ i : ℝ) : ℂ) * w i := by
  simp [PiLp.inner_apply, freqVec_apply, Complex.conj_ofReal, mul_comm]

theorem varConstMap_solenoidal {a : ℝ} {F₀ : Space → CSpace} {G : ℝ → Space → CSpace} {t : ℝ}
    (h0 : IsSolenoidalSymbol F₀) (hG : ∀ s ∈ uIcc a t, ∀ᵐ η ∂volume, G s (-η) = conjVec (G s η)) :
    IsSolenoidalSymbol (varConstMap a F₀ G t) := by
  have hr : ∀ r : ℝ, star ((r : ℂ)) = r := fun r => Complex.conj_ofReal r
  intro ξ
  constructor
  · rw [← inner_freqVec]
    simp only [varConstMap, inner_add_right, inner_smul_right]
    rw [inner_freqVec, (h0 ξ).1, mul_zero, zero_add]
    by_cases hi : IntervalIntegrable (fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (G s) ξ)
      volume a t
    · have hc := (innerSL ℂ (freqVec ξ)).intervalIntegral_comp_comm hi
      change (innerSL ℂ (freqVec ξ)) _ = 0
      rw [← hc]
      simp [inner_freqVec, nonlinSymbol_div]
    · rw [intervalIntegral.integral_undef hi, inner_zero_right]
  · simp only [varConstMap, heatSymbol, norm_neg, map_add]
    congr 1
    · rw [(h0 ξ).2]
      ext i
      simp only [conjVec_apply, PiLp.smul_apply, smul_eq_mul, star_mul', hr]
    · have : ∀ s ∈ uIcc a t, ((Real.exp (-(4 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2)) : ℝ) : ℂ) •
          nonlinSymbol (G s) (-ξ) = conjVecIso (((Real.exp (-(4 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2)) : ℝ) : ℂ) •
          nonlinSymbol (G s) ξ) := by
        intro s hs
        rw [nonlinSymbol_neg (hG s hs)]
        ext i
        change _ = conjVec _ i
        simp only [conjVec_apply, PiLp.smul_apply, smul_eq_mul, star_mul', hr]
      rw [intervalIntegral.integral_congr this, LinearIsometry.intervalIntegral_comp_comm]
      rfl

end Breakdown.SmoothFlow
