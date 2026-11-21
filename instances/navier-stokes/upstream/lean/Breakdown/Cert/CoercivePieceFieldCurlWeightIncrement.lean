import Breakdown.Defs

open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace CurlWeight.Internal

theorem increment_weightSum {n : ℕ} (c : Fin n → ℝ) (f : Fin n → Space → ℝ) (hf : ∀ β, ∃ K, LipschitzWith K (f β)) :
    ∃ K : NNReal, LipschitzWith K (fun y => ∑ β, c β * f β y) := by
  choose K hK using hf
  refine ⟨∑ β, ‖c β‖₊ * K β, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  push_cast
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  have h := (hK β).dist_le_mul x y
  rw [Real.dist_eq] at h
  rw [← mul_sub, abs_mul, mul_assoc, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem sum_sq_apply_unitVector_le (L : Space →L[ℝ] ℝ) :
    ∑ j : Fin 3, (L (unitVector j)) ^ 2 ≤ ‖L‖ ^ 2 := by
  set q : Space := ∑ j : Fin 3, L (unitVector j) • unitVector j with hq
  have hLq : L q = ∑ j : Fin 3, (L (unitVector j)) ^ 2 := by
    rw [hq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, sq]
  have hqc : ∀ i, q i = L (unitVector i) := by
    intro i
    rw [hq]
    simp [unitVector, Pi.single_apply]
  have hnq : ‖q‖ ^ 2 = ∑ j : Fin 3, (L (unitVector j)) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, hqc]
  have hle : ‖q‖ ^ 2 ≤ ‖L‖ * ‖q‖ := by
    rw [hnq, ← hLq]
    exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact L.le_opNorm q)
  rw [← hnq]
  rcases (norm_nonneg q).eq_or_lt with h0 | hpos
  · rw [← h0]
    nlinarith [sq_nonneg ‖L‖]
  · have : ‖q‖ ≤ ‖L‖ := by
      rw [sq] at hle
      exact le_of_mul_le_mul_right hle hpos
    exact pow_le_pow_left₀ (norm_nonneg q) this 2

theorem ae_lineDeriv_sq_le {n : ℕ} (c : Fin n → ℝ) (f : Fin n → Space → ℝ) (hf : ∀ β, ∃ K, LipschitzWith K (f β)) {A' : ℝ}
    (hA' : ∀ y, (∀ β, DifferentiableAt ℝ (f β) y) → ‖fderiv ℝ (fun x => ∑ β, c β * f β x) y‖ ≤ A') :
    ∀ᵐ y, ∑ j : Fin 3, (lineDeriv ℝ (fun x => ∑ β, c β * f β x) y (unitVector j)) ^ 2 ≤ A' ^ 2 ∧ 0 ≤ A' := by
  have hd : ∀ᵐ y, ∀ β, DifferentiableAt ℝ (f β) y := by
    rw [ae_all_iff]
    intro β
    obtain ⟨K, hK⟩ := hf β
    exact hK.ae_differentiableAt
  filter_upwards [hd] with y hy
  have hs : DifferentiableAt ℝ (fun x => ∑ β, c β * f β x) y := by
    have : DifferentiableAt ℝ (∑ β, fun x => c β * f β x) y :=
      DifferentiableAt.sum fun β _ => (hy β).const_mul (c β)
    convert this using 1
    funext x
    simp
  have hb := hA' y hy
  have h0 : 0 ≤ A' := (norm_nonneg _).trans hb
  refine ⟨?_, h0⟩
  have e : ∀ j, lineDeriv ℝ (fun x => ∑ β, c β * f β x) y (unitVector j) =
      fderiv ℝ (fun x => ∑ β, c β * f β x) y (unitVector j) := fun j => hs.lineDeriv_eq_fderiv
  simp only [e]
  exact (sum_sq_apply_unitVector_le _).trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end CurlWeight.Internal

end Coercive

end Breakdown
