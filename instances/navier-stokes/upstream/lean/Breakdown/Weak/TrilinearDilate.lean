import Breakdown.Weak.StatementsSlice

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.WeakProfile

open Freq

theorem trilinearDilate_holds : TrilinearDilate := by
  intro _ μ hμ x ψ _
  have hc : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have h3 : Real.sqrt μ ^ 3 = μ * Real.sqrt μ := by rw [pow_succ, Real.sq_sqrt hμ.le]
  unfold trilinear
  have hU := velocityCov_holds.2 μ hμ x
  have hV : ∀ᵐ y ∂volume, ∀ j : Fin 3, (partialX j (dilX μ x) : Space → Space) y =
      μ • (partialX j x : Space → Space) (Real.sqrt μ • y) :=
    ae_all_iff.2 (fun j =>
      Internal.BilinDilate.partialX_dilX dilation_holds fieldOpRealized_holds hμ j x)
  let G : Space → ℝ := fun z => ∑ j : Fin 3, (velocity x : Space → Space) z j *
    inner ℝ ((partialX j x : Space → Space) z) (spaceScale (Real.sqrt μ)⁻¹ ψ z)
  have e1 : (fun y => ∑ j : Fin 3, (velocity (dilX μ x) : Space → Space) y j *
      inner ℝ ((partialX j (dilX μ x) : Space → Space) y) (ψ y)) =ᵐ[volume]
      fun y => Real.sqrt μ ^ 3 * G (Real.sqrt μ • y) := by
    filter_upwards [hU, hV] with y h1 h2
    simp only [G, spaceScale, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h1, h2 j, dilateField, PiLp.smul_apply, smul_eq_mul, real_inner_smul_left, h3]
    ring
  have e2 : ∫ y, Real.sqrt μ ^ 3 * G (Real.sqrt μ • y) = ∫ z, G z := by
    rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace, Fintype.card_fin,
      smul_eq_mul, abs_of_pos (by positivity)]
    field_simp
  exact (integral_congr_ae e1).trans e2

end Breakdown.WeakProfile
