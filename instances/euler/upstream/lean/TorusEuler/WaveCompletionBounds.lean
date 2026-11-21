import TorusEuler.WaveCompletionRelay
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-! Order-zero phase bounds for the curl potential and its time derivative. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler

local notation "V₃" => EuclideanSpace ℝ (Fin 3)

noncomputable section

theorem norm_cross3_le (k v : V₃) : ‖cross3 k v‖ ≤ ‖k‖ * ‖v‖ := by
  rw [cross3, InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg k) (norm_nonneg v)) (Real.sin_le_one _)

private theorem norm_neg_inv_normsq_smul_cross3_le {κ : V₃} (hn : κ ≠ 0) (v : V₃) :
    ‖(-(‖κ‖ ^ 2)⁻¹) • cross3 κ v‖ ≤ ‖v‖ / ‖κ‖ := by
  have hk : 0 < ‖κ‖ := norm_pos_iff.mpr hn
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (‖κ‖ ^ 2)⁻¹)]
  refine (mul_le_mul_of_nonneg_left (norm_cross3_le κ v) (by positivity)).trans_eq ?_
  field_simp

private theorem phaseMean_comp_clm (A : V₃ →L[ℝ] V₃) {V : ℝ → V₃}
    (hV : Continuous V) : phaseMean (fun r => A (V r)) = A (phaseMean V) := by
  simpa only [phaseMean, Function.comp_apply] using
    A.intervalIntegral_comp_comm (hV.intervalIntegrable 0 1)

/-- A fixed-label potential costs one inverse covector size. -/
theorem norm_wavePotential_le {κ : V₃} (hn : κ ≠ 0) {V : ℝ → V₃}
    (hc : Continuous V) (hp : Function.Periodic V 1) (hm : phaseMean V = 0)
    {B : ℝ} (hB : ∀ s ∈ Icc (0 : ℝ) 1, ‖V s‖ ≤ B) (s : ℝ) :
    ‖wavePotential κ V s‖ ≤ 2 * B / ‖κ‖ := by
  let A := (-(‖κ‖ ^ 2)⁻¹) • cross3Left κ
  have hAc : Continuous (fun z => A (V z)) := A.continuous.comp hc
  have hAm : phaseMean (fun z => A (V z)) = 0 := by
    rw [phaseMean_comp_clm A hc, hm, map_zero]
  rw [mul_div_assoc]
  exact norm_phasePrimitive_le hAc (fun z => congrArg A (hp z)) hAm
    (fun r hr => (norm_neg_inv_normsq_smul_cross3_le hn (V r)).trans
      (div_le_div_of_nonneg_right (hB r hr) (norm_nonneg κ))) s

/-- The derivative of the potential integrand has the same inverse covector scale.
The factor involving the forcing is independent of any pressure derivative. -/
theorem norm_wavePotentialTimeSource_le (M : V₃ →L[ℝ] V₃) {κ : V₃}
    (hn : κ ≠ 0) (v f : V₃) :
    ‖wavePotentialTimeSource M κ v f‖ ≤ (4 * ‖M‖ * ‖v‖ + ‖f‖) / ‖κ‖ := by
  have hk : 0 < ‖κ‖ := norm_pos_iff.mpr hn
  have hAdj : ‖M.adjoint κ‖ ≤ ‖M‖ * ‖κ‖ := by
    simpa only [LinearIsometryEquiv.norm_map] using M.adjoint.le_opNorm κ
  have hsum : ‖cross3 (M.adjoint κ) v + cross3 κ (M v) - cross3 κ f‖ ≤
      (‖M‖ * ‖κ‖) * ‖v‖ + ‖κ‖ * (‖M‖ * ‖v‖) + ‖κ‖ * ‖f‖ :=
    (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_cross3_le _ _).trans
        (mul_le_mul_of_nonneg_right hAdj (norm_nonneg _)))
        ((norm_cross3_le _ _).trans (mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)))))
      (norm_cross3_le _ _))
  have hInner : |⟪κ, M κ⟫_ℝ| ≤ ‖κ‖ * (‖M‖ * ‖κ‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _))
  have hFac : |2 * ⟪κ, M κ⟫_ℝ / (‖κ‖ ^ 2) ^ 2| ≤
      2 * (‖κ‖ * (‖M‖ * ‖κ‖)) / (‖κ‖ ^ 2) ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by positivity : 0 ≤ (‖κ‖ ^ 2) ^ 2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hInner (by norm_num)) (by positivity)
  unfold wavePotentialTimeSource
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (‖κ‖ ^ 2)⁻¹)]
  refine (add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity))
    (mul_le_mul hFac (norm_cross3_le _ _) (norm_nonneg _) (by positivity))).trans_eq ?_
  field_simp
  ring

private theorem wavePotentialTimeSource_linear (M : V₃ →L[ℝ] V₃) (κ : V₃) :
    ∃ A B : V₃ →L[ℝ] V₃, ∀ v f, wavePotentialTimeSource M κ v f = A v + B f := by
  refine ⟨(‖κ‖ ^ 2)⁻¹ • (cross3Left (M.adjoint κ) + (cross3Left κ).comp M) -
    (2 * ⟪κ, M κ⟫_ℝ / (‖κ‖ ^ 2) ^ 2) • cross3Left κ,
    -(‖κ‖ ^ 2)⁻¹ • cross3Left κ, ?_⟩
  intro v f
  simp only [wavePotentialTimeSource, sub_apply, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply, cross3Left_apply,
    smul_sub, neg_smul]
  abel

/-- The primitive in (5.33) gains one inverse covector size without a time derivative
of the forcing or of the strain. -/
theorem norm_phasePrimitive_wavePotentialTimeSource_le (M : V₃ →L[ℝ] V₃) {κ : V₃}
    (hn : κ ≠ 0) {V F : ℝ → V₃}
    (hVc : Continuous V) (hFc : Continuous F)
    (hVp : Function.Periodic V 1) (hFp : Function.Periodic F 1)
    (hVm : phaseMean V = 0) (hFm : phaseMean F = 0) {BV BF : ℝ}
    (hBV : ∀ s ∈ Icc (0 : ℝ) 1, ‖V s‖ ≤ BV) (hBF : ∀ s ∈ Icc (0 : ℝ) 1, ‖F s‖ ≤ BF)
    (s : ℝ) :
    ‖phasePrimitive (fun r => wavePotentialTimeSource M κ (V r) (F r)) s‖ ≤
      2 * (4 * ‖M‖ * BV + BF) / ‖κ‖ := by
  obtain ⟨A, B, hAB⟩ := wavePotentialTimeSource_linear M κ
  have hAc : Continuous (fun r => A (V r)) := A.continuous.comp hVc
  have hBc : Continuous (fun r => B (F r)) := B.continuous.comp hFc
  have hEq : (fun r => wavePotentialTimeSource M κ (V r) (F r)) =
      (fun r => A (V r) + B (F r)) := funext (fun r => hAB (V r) (F r))
  have hCont : Continuous (fun r => wavePotentialTimeSource M κ (V r) (F r)) := by
    rw [hEq]
    exact hAc.add hBc
  have hPer : Function.Periodic (fun r => wavePotentialTimeSource M κ (V r) (F r)) 1 :=
    fun r => by simp only [hVp r, hFp r]
  have hMean : phaseMean (fun r => wavePotentialTimeSource M κ (V r) (F r)) = 0 := by
    rw [hEq, phaseMean_add hAc hBc, phaseMean_comp_clm A hVc, phaseMean_comp_clm B hFc,
      hVm, hFm, map_zero, map_zero, add_zero]
  rw [mul_div_assoc]
  refine norm_phasePrimitive_le hCont hPer hMean (fun r hr => ?_) s
  exact (norm_wavePotentialTimeSource_le M hn (V r) (F r)).trans
    (div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left (hBV r hr) (by positivity)) (hBF r hr)) (norm_nonneg _))

end

end TorusEuler
