import Breakdown.Defs

open Real

noncomputable section

namespace Breakdown.Cert

theorem norm_double_sum_le (v w : Space) (c : Fin 3 → Fin 3 → Space) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, (v i * w j) • c i j‖ ≤
      ‖v‖ * ‖w‖ * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ‖c i j‖ ^ 2) := by
  have h1 : ‖∑ i : Fin 3, ∑ j : Fin 3, (v i * w j) • c i j‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), (|v p.1| * |w p.2|) * ‖c p.1 p.2‖ := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p => |v p.1| * |w p.2|) (fun p => ‖c p.1 p.2‖)
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), (|v p.1| * |w p.2|) ^ 2 =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp_rw [mul_pow, sq_abs]
    rw [← Finset.sum_mul_sum, EuclideanSpace.norm_eq v, EuclideanSpace.norm_eq w,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    simp
  have h4 : ∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), ‖c p.1 p.2‖ ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, ‖c i j‖ ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [h3, h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at h2
  linarith

end Breakdown.Cert
