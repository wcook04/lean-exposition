import Breakdown.FracCell.ReductionLossDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace AdjointQuadInternal

theorem apply_norm_le (A : Space →L[ℝ] Space) (x : Space) :
    ‖A x‖ ≤ Real.sqrt (entrySq A) * ‖x‖ := by
  have hx : x = ∑ j : Fin 3, x j • unitVector j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
    simp [unitVector, EuclideanSpace.basisFun_apply]
  have h1 : ‖A x‖ ≤ ∑ j : Fin 3, |x j| * ‖A (unitVector j)‖ := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |x j|) (fun j => ‖A (unitVector j)‖)
  have h3 : ‖x‖ = Real.sqrt (∑ j : Fin 3, |x j| ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs]
  calc ‖A x‖ ≤ _ := h1
    _ ≤ _ := h2
    _ = Real.sqrt (entrySq A) * ‖x‖ := by rw [h3, entrySq, mul_comm]

theorem entrySq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem amgm {a b t : ℝ} (ht : 0 < t) : a * b ≤ t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 := by
  have h : t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 - a * b = (t * a - b) ^ 2 / (2 * t) := by
    field_simp
    ring
  have : 0 ≤ (t * a - b) ^ 2 / (2 * t) := by positivity
  linarith

theorem pointwise {w eS V nu nz ip t : ℝ} (ht : 0 < t) (hw : 0 ≤ w) (hV : 0 ≤ V) (heS : 0 ≤ eS)
    (hnu : 0 ≤ nu) (hip : |ip| ≤ Real.sqrt eS * nu * nz) (hz : nz ^ 2 ≤ w * V) :
    |ip| ≤ t / 2 * (w * eS) + 1 / (2 * t) * (V * nu ^ 2) := by
  have hz' : nz ≤ Real.sqrt w * Real.sqrt V := by
    rw [← Real.sqrt_mul hw]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hz)
  have h1 : |ip| ≤ (Real.sqrt w * Real.sqrt eS) * (Real.sqrt V * nu) := by
    calc |ip| ≤ Real.sqrt eS * nu * nz := hip
      _ ≤ Real.sqrt eS * nu * (Real.sqrt w * Real.sqrt V) :=
        mul_le_mul_of_nonneg_left hz' (mul_nonneg (Real.sqrt_nonneg _) hnu)
      _ = _ := by ring
  have h2 := amgm (a := Real.sqrt w * Real.sqrt eS) (b := Real.sqrt V * nu) ht
  have e1 : (Real.sqrt w * Real.sqrt eS) ^ 2 = w * eS := by
    rw [mul_pow, Real.sq_sqrt hw, Real.sq_sqrt heS]
  have e2 : (Real.sqrt V * nu) ^ 2 = V * nu ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hV]
  rw [e1, e2] at h2
  linarith

end AdjointQuadInternal

open AdjointQuadInternal in
theorem adjointQuad_of_potential (hK : KernelPotentialStatement) {k N : ℕ} (d : FracCertData k N)
    (hw : 0 < d.weightMin) (hlow : ∀ y, d.weightMin ≤ d.weight y) (hmeas : Measurable d.weight)
    (hhigh : ∀ y, d.weight y ≤ d.weightMax) (V : Fin k → (Fin k → ℝ) → Space → ℝ) (Λ : Fin k → (Fin k → ℝ) → ℝ)
    (hζ : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, AEStronglyMeasurable (d.adjoint j p) volume)
    (hV : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ y, ‖d.adjoint j p y‖ ^ 2 ≤ d.weight y * V j p y)
    (hKV : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, KernelBound (V j p) (Λ j p))
    (hbound : ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, Real.sqrt (Λ j p) / Real.sqrt d.weightMin ≤ d.adjointQuad j p) :
    ∀ j ∈ d.activeSet, ∀ p ∈ box d.radius, ∀ u G H, IsSecondOrderField d.order u G H →
      |l2Pair (fun y => G y (u y)) (d.adjoint j p)| ≤ d.adjointQuad j p * d.energy G H := by
  intro j hj p hp u G H hs
  have hpair : IsGradientPair u G :=
    ⟨hs.measurable_velocity, hs.velocity_six, hs.measurable_gradient, hs.gradient_two, hs.weak_gradient⟩
  obtain ⟨hBi, hB⟩ := hK _ _ (hKV j hj p hp) u G hpair
  have hVnn : ∀ y, 0 ≤ V j p y := (hKV j hj p hp).1
  have hS := hs.gradient_two
  have hwnn : ∀ y, 0 ≤ d.weight y := fun y => hw.le.trans (hlow y)
  have hAi : Integrable (fun y => d.weight y * entrySq (G y)) := by
    refine hS.bdd_mul (c := d.weightMax) hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hwnn y)]
    exact hhigh y
  have hS0 : 0 ≤ ∫ y, entrySq (G y) := integral_nonneg fun y => entrySq_nonneg _
  have hSA : d.weightMin * ∫ y, entrySq (G y) ≤ ∫ y, d.weight y * entrySq (G y) := by
    rw [← integral_const_mul]
    exact integral_mono (hS.const_mul _) hAi fun y => mul_le_mul_of_nonneg_right (hlow y) (entrySq_nonneg _)
  have hA0 : 0 ≤ ∫ y, d.weight y * entrySq (G y) := le_trans (mul_nonneg hw.le hS0) hSA
  have hQ0 : 0 ≤ d.adjointQuad j p :=
    le_trans (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hbound j hj p hp)
  have hΛ : Λ j p ≤ d.adjointQuad j p ^ 2 * d.weightMin := by
    rcases le_or_gt (Λ j p) 0 with h | h
    · exact h.trans (mul_nonneg (sq_nonneg _) hw.le)
    · have hsw : 0 < Real.sqrt d.weightMin := Real.sqrt_pos.2 hw
      have h1 : Real.sqrt (Λ j p) ≤ d.adjointQuad j p * Real.sqrt d.weightMin :=
        (div_le_iff₀ hsw).1 (hbound j hj p hp)
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [Real.sq_sqrt h.le, mul_pow, Real.sq_sqrt hw.le] at h2
      exact h2
  have hBQ : (∫ y, V j p y * ‖u y‖ ^ 2) ≤ d.adjointQuad j p ^ 2 * ∫ y, d.weight y * entrySq (G y) := by
    calc (∫ y, V j p y * ‖u y‖ ^ 2) ≤ Λ j p * ∫ y, entrySq (G y) := hB
      _ ≤ (d.adjointQuad j p ^ 2 * d.weightMin) * ∫ y, entrySq (G y) := mul_le_mul_of_nonneg_right hΛ hS0
      _ = d.adjointQuad j p ^ 2 * (d.weightMin * ∫ y, entrySq (G y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hSA (sq_nonneg _)
  have key : ∀ t : ℝ, 0 < t → |l2Pair (fun y => G y (u y)) (d.adjoint j p)| ≤
      t / 2 * (∫ y, d.weight y * entrySq (G y)) + 1 / (2 * t) * ∫ y, V j p y * ‖u y‖ ^ 2 := by
    intro t ht
    have hgi : Integrable (fun y => t / 2 * (d.weight y * entrySq (G y)) + 1 / (2 * t) * (V j p y * ‖u y‖ ^ 2)) :=
      (hAi.const_mul _).add (hBi.const_mul _)
    have h := norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun y =>
      (show ‖inner ℝ (G y (u y)) (d.adjoint j p y)‖ ≤ _ by
        rw [Real.norm_eq_abs]
        refine pointwise ht (hwnn y) (hVnn y) (entrySq_nonneg _) (norm_nonneg _) ?_ (hV j hj p hp y)
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (apply_norm_le _ _) (norm_nonneg _))))
    rw [integral_add (hAi.const_mul _) (hBi.const_mul _), integral_const_mul, integral_const_mul] at h
    rw [← Real.norm_eq_abs]
    exact h
  have hT : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hmain : |l2Pair (fun y => G y (u y)) (d.adjoint j p)| ≤
      d.adjointQuad j p * ∫ y, d.weight y * entrySq (G y) := by
    rcases hQ0.lt_or_eq with hQp | hQz
    · have h := key _ hQp
      have h2 : 1 / (2 * d.adjointQuad j p) * (∫ y, V j p y * ‖u y‖ ^ 2) ≤
          d.adjointQuad j p / 2 * ∫ y, d.weight y * entrySq (G y) := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · have hB0 : (∫ y, V j p y * ‖u y‖ ^ 2) ≤ 0 := by
        rw [← hQz] at hBQ
        simpa using hBQ
      rw [← hQz, zero_mul]
      refine le_of_not_gt fun hc => ?_
      have hA1 : 0 < (∫ y, d.weight y * entrySq (G y)) + 1 := by linarith
      have ht := div_pos hc hA1
      have h := key _ ht
      have hneg := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (one_div_pos.2 (mul_pos two_pos ht))) hB0
      have hmul := div_mul_cancel₀ |l2Pair (fun y => G y (u y)) (d.adjoint j p)| hA1.ne'
      nlinarith
  calc _ ≤ d.adjointQuad j p * ∫ y, d.weight y * entrySq (G y) := hmain
    _ ≤ d.adjointQuad j p * d.energy G H := by
      refine mul_le_mul_of_nonneg_left ?_ hQ0
      show _ ≤ weightedEnergy d.weight G H
      unfold weightedEnergy
      linarith

end Reduction

end CellCert

end Breakdown
