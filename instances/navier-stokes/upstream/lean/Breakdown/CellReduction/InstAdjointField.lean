import Breakdown.CellReduction.InstanceStatements
import Breakdown.CellReduction.PotGenerator
import Breakdown.CertCell.CellLayerClosed

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape AdjointDefect

namespace Internal

theorem le_div_rpow_of_pow {a C C' e : ℝ} {n : ℕ} (y : Space) (h : a ≤ C / (1 + ‖y‖) ^ n)
    (hC : C ≤ C') (he : (n : ℝ) = e) : a ≤ C' / (1 + ‖y‖) ^ e := by
  rw [← he, Real.rpow_natCast]
  exact h.trans (div_le_div_of_nonneg_right hC (by positivity))

theorem le_div_pow_of_le_exp {a C : ℝ} {m n : ℕ} (y : Space) (hC : 0 ≤ C) (hmn : m ≤ n)
    (h : a ≤ C / (1 + ‖y‖) ^ n) : a ≤ C / (1 + ‖y‖) ^ m :=
  h.trans (div_le_div_of_nonneg_left hC (by positivity)
    (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg y)) hmn))

end Internal

theorem secondDerivAgree_from_keys : SecondDerivAgreeHolds := fun P D hP hD σ =>
  PotentialShape.Internal.secondDeriv_ae_eq_givenSecond P D σ
    (PotentialShape.Internal.keysSmooth_of_data P D σ hP hD)

theorem adjointField_holds_of (hdec : FieldDecayOrderHolds) (hpot : FieldPotentialHolds)
    (hdiv : ClassicalDivergenceWeakHolds) : AdjointFieldHolds := by
  intro k _ nE nM D Z hZ
  refine ⟨?_, ?_⟩
  · intro j hj q σ φ hφ
    rw [hZ.adjoint_eq j hj q]
    have hF := (shapeParts_closed.field_smooth Z.params (Z.field j) hZ.params_valid (hZ.field_valid j hj)).1
    exact hdiv _ (hF.comp (contDiff_const.prodMk contDiff_id))
      (shapeParts_closed.field_divergence Z.params (Z.field j) hZ.params_valid (hZ.field_valid j hj) σ) φ hφ
  · intro j hj
    have hP := hZ.params_valid
    have hD := hZ.field_valid j hj
    have hhigh := hZ.highOrder_ge j hj
    obtain ⟨C₁, hB⟩ := hdec Z.params (Z.field j) 3 hP hD hhigh
    obtain ⟨A, C₂, hAs, hAp, hAc, hAd⟩ := hpot Z.params (Z.field j) hP hD hhigh
    have hC₁ : 0 ≤ C₁ := by
      have h := (hB 0 0).1
      rw [norm_zero, add_zero, one_pow, div_one] at h
      exact (norm_nonneg _).trans h
    have hsm := shapeParts_closed.field_smooth Z.params (Z.field j) hP hD
    have hae := fun σ => secondDerivAgree_from_keys Z.params (Z.field j) hP hD σ
    refine ⟨A, max C₁ C₂, fun q => ?_, fun q => ?_⟩
    · rw [hZ.adjoint_eq j hj q]
      refine
        { rate_gt := by norm_num
          smooth := hsm.1
          periodic := hsm.2.1
          divergence_free := shapeParts_closed.field_divergence Z.params (Z.field j) hP hD
          second_weak := fun σ i => ?_
          decay := fun σ y => ⟨?_, ?_, ?_⟩
          second_decay := fun σ => ?_
          second_differentiable := fun σ => ?_ }
      · refine PotentialShape.Internal.weakGradient_congr_ae
          (shapeParts_closed.field_weak_hessian Z.params (Z.field j) hP hD σ i) ?_
        filter_upwards [hae σ] with y hy
        rw [hy.2]
      · exact Internal.le_div_rpow_of_pow y (hB σ y).1 (le_max_left _ _) (by norm_num)
      · exact Internal.le_div_rpow_of_pow y (hB σ y).2.1 (le_max_left _ _) (by norm_num)
      · exact Internal.le_div_rpow_of_pow y (hB σ y).2.2.1 (le_max_left _ _) (by norm_num)
      · filter_upwards [hae σ] with y hy
        rw [hy.2]
        exact Internal.le_div_rpow_of_pow y
          (Internal.le_div_pow_of_le_exp (m := 3) y hC₁ (by norm_num) (hB σ y).2.2.2)
          (le_max_left _ _) (by norm_num)
      · filter_upwards [hae σ] with y hy
        exact hy.1
    · rw [hZ.adjoint_eq j hj q]
      refine
        { rate_gt := by norm_num
          smooth := hAs
          periodic := hAp
          curl_eq := hAc
          decay := fun σ y => ⟨?_, ?_, ?_⟩ }
      · exact Internal.le_div_rpow_of_pow y (hAd σ y).1 (le_max_right _ _) (by norm_num)
      · exact Internal.le_div_rpow_of_pow y (hAd σ y).2.1 (le_max_right _ _) (by norm_num)
      · exact Internal.le_div_rpow_of_pow y (hAd σ y).2.2 (le_max_right _ _) (by norm_num)

end Instantiation

end CellReduction

end Breakdown
