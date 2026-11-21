import Breakdown.Frac.StProfile
import Breakdown.Frac.OpCovariance

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal

theorem rigidScale_power (α : ℝ) (U : Space → Space) (hU : ContDiff ℝ 2 U)
    (R : Space ≃ₗᵢ[ℝ] Space) (c l : ℝ) (hl : 0 < l) (x : Space) :
    fractionalPowerAt α (fun y => c • R (U (R.symm (l • y)))) x =
      (c * l ^ (2 * α)) • R (fractionalPowerAt α U (R.symm (l • x))) := by
  have hV : ContDiff ℝ 2 (fun z => R (U (R.symm z))) :=
    R.toContinuousLinearEquiv.contDiff.comp (hU.comp R.symm.toContinuousLinearEquiv.contDiff)
  have hVl : ContDiff ℝ 2 (fun y => R (U (R.symm (l • y)))) :=
    hV.comp (contDiff_const_smul l)
  have e1 := (covariance α _ hVl).2.1 c x
  have e2 := (covariance α _ hV).1 l hl x
  have e3 := (covariance α U hU).2.2.1 R (l • x)
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, smul_smul]

theorem rigidScale_fderiv_apply (U : Space → Space) (hU : Differentiable ℝ U)
    (R : Space ≃ₗᵢ[ℝ] Space) (c l : ℝ) (x v : Space) :
    fderiv ℝ (fun y => c • R (U (R.symm (l • y)))) x v =
      c • R (fderiv ℝ U (R.symm (l • x)) (R.symm (l • v))) := by
  have hs : HasFDerivAt (fun y : Space => l • y) (l • ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id x).const_smul l
  have h : HasFDerivAt (fun y => c • R (U (R.symm (l • y))))
      (c • ((R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((fderiv ℝ U (R.symm (l • x))).comp
          ((R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
            (l • ContinuousLinearMap.id ℝ Space))))) x :=
    (R.toContinuousLinearEquiv.hasFDerivAt.comp x
      ((hU (R.symm (l • x))).hasFDerivAt.comp x
        (R.symm.toContinuousLinearEquiv.hasFDerivAt.comp x hs))).const_smul c
  rw [h.fderiv]
  rfl

theorem rigidScale_scalar_fderiv_apply (P : Space → ℝ) (hP : Differentiable ℝ P)
    (Q : Space ≃ₗᵢ[ℝ] Space) (k l : ℝ) (x v : Space) :
    fderiv ℝ (fun y => k * P (Q (l • y))) x v = k * fderiv ℝ P (Q (l • x)) (Q (l • v)) := by
  have hs : HasFDerivAt (fun y : Space => l • y) (l • ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id x).const_smul l
  have h : HasFDerivAt (fun y => k * P (Q (l • y)))
      (k • ((fderiv ℝ P (Q (l • x))).comp
          ((Q.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
            (l • ContinuousLinearMap.id ℝ Space)))) x :=
    ((hP (Q (l • x))).hasFDerivAt.comp x
        (Q.toContinuousLinearEquiv.hasFDerivAt.comp x hs)).const_mul k
  rw [h.fderiv]
  rfl

private theorem gradientAt_norm_le_sum (p : Space → ℝ) (x : Space) :
    ‖gradientAt p x‖ ≤ ∑ i : Fin 3, |fderiv ℝ p x (unitVector i)| := by
  unfold gradientAt
  refine (norm_sum_le _ _).trans ?_
  gcongr with i
  rw [norm_smul]
  simp [unitVector]

theorem rigidScale_residual_bound (α : ℝ) (hα : 1 < α) (U : Space → Space) (P : Space → ℝ)
    (hU : ContDiff ℝ ∞ U) (hP : ContDiff ℝ ∞ P) (R Q : Space ≃ₗᵢ[ℝ] Space) (μ : ℝ) (hμ : 1 ≤ μ)
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hA : ∀ y, ‖fractionalPowerAt α U y‖ ≤ D * (1 + ‖y‖) ^ (-(4 * α - 1)))
    (h0 : ∀ y, ‖U y‖ ≤ D * (1 + ‖y‖) ^ (-(2 * α - 1)))
    (h1 : ∀ y, ‖fderiv ℝ U y‖ ≤ E * (1 + ‖y‖) ^ (-(2 * α)))
    (hp : ∀ y, ‖fderiv ℝ P y‖ ≤ D * (1 + ‖y‖) ^ (-(4 * α - 1))) (x : Space) :
    ‖-fractionalPowerAt α
        (fun y => μ ^ (1 - 1 / (2 * α)) • R (U (R.symm (μ ^ (1 / (2 * α)) • y)))) x
      - advectionAt (fun y => μ ^ (1 - 1 / (2 * α)) • R (U (R.symm (μ ^ (1 / (2 * α)) • y)))) x
      - gradientAt (fun y => μ ^ (2 - 1 / α) * P (Q (μ ^ (1 / (2 * α)) • y))) x‖ ≤
      μ ^ (2 - 1 / (2 * α)) * (D + E * D + 3 * D) * (1 + ‖x‖) ^ (-(4 * α - 1)) := by
  have hα0 : 0 < α := by linarith
  have hμ0 : 0 < μ := by linarith
  have hl1 : 1 ≤ μ ^ (1 / (2 * α)) := Real.one_le_rpow hμ (by positivity)
  have e1 : μ ^ (1 - 1 / (2 * α)) * (μ ^ (1 / (2 * α))) ^ (2 * α) = μ ^ (2 - 1 / (2 * α)) := by
    rw [← Real.rpow_mul hμ0.le, ← Real.rpow_add hμ0]
    congr 1
    field_simp
    ring
  have e2 : μ ^ (1 - 1 / (2 * α)) * μ ^ (1 - 1 / (2 * α)) * μ ^ (1 / (2 * α)) =
      μ ^ (2 - 1 / (2 * α)) := by
    rw [← Real.rpow_add hμ0, ← Real.rpow_add hμ0]
    congr 1
    ring
  have e3 : μ ^ (2 - 1 / α) * μ ^ (1 / (2 * α)) = μ ^ (2 - 1 / (2 * α)) := by
    rw [← Real.rpow_add hμ0]
    congr 1
    field_simp
    ring
  obtain ⟨c, hc⟩ : ∃ c, c = μ ^ (1 - 1 / (2 * α)) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = μ ^ (1 / (2 * α)) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = μ ^ (2 - 1 / α) := ⟨_, rfl⟩
  rw [← hc, ← hl, ← hk]
  rw [← hc, ← hl] at e1 e2
  rw [← hk, ← hl] at e3
  rw [← hl] at hl1
  have hc0 : 0 < c := hc ▸ Real.rpow_pos_of_pos hμ0 _
  have hl0 : 0 < l := hl ▸ Real.rpow_pos_of_pos hμ0 _
  have hk0 : 0 < k := hk ▸ Real.rpow_pos_of_pos hμ0 _
  have hU2 : ContDiff ℝ 2 U := hU.of_le (WithTop.coe_le_coe.mpr le_top)
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hPd : Differentiable ℝ P := hP.differentiable (by simp)
  have hb0 : 0 < 1 + l * ‖x‖ := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hl0.le (norm_nonneg x))
  have hbx : (1 + l * ‖x‖) ^ (-(4 * α - 1)) ≤ (1 + ‖x‖) ^ (-(4 * α - 1)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [norm_nonneg x]) (by linarith)
  have hy : ‖R.symm (l • x)‖ = l * ‖x‖ := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg hl0.le]
  have hy' : ‖Q (l • x)‖ = l * ‖x‖ := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg hl0.le]
  have bA : ‖fractionalPowerAt α (fun y => c • R (U (R.symm (l • y)))) x‖ ≤
      μ ^ (2 - 1 / (2 * α)) * D * (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by
    rw [rigidScale_power α U hU2 R c l hl0 x, norm_smul, LinearIsometryEquiv.norm_map,
      Real.norm_of_nonneg (mul_pos hc0 (Real.rpow_pos_of_pos hl0 _)).le, e1, mul_assoc]
    gcongr
    have := hA (R.symm (l • x))
    rwa [hy] at this
  have bB : ‖advectionAt (fun y => c • R (U (R.symm (l • y)))) x‖ ≤
      μ ^ (2 - 1 / (2 * α)) * (E * D) * (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by
    unfold advectionAt
    beta_reduce
    rw [rigidScale_fderiv_apply U hUd R c l x, norm_smul, LinearIsometryEquiv.norm_map,
      Real.norm_of_nonneg hc0.le]
    have hv : R.symm (l • (c • R (U (R.symm (l • x))))) = (l * c) • U (R.symm (l • x)) := by
      rw [smul_smul, map_smul, LinearIsometryEquiv.symm_apply_apply]
    rw [hv]
    have q1 := h1 (R.symm (l • x))
    have q0 := h0 (R.symm (l • x))
    rw [hy] at q1 q0
    have hexp : (1 + l * ‖x‖) ^ (-(2 * α)) * (1 + l * ‖x‖) ^ (-(2 * α - 1)) =
        (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by
      rw [← Real.rpow_add hb0]
      congr 1
      ring
    have hlc : 0 ≤ l * c := (mul_pos hl0 hc0).le
    calc c * ‖fderiv ℝ U (R.symm (l • x)) ((l * c) • U (R.symm (l • x)))‖
        ≤ c * (‖fderiv ℝ U (R.symm (l • x))‖ * ‖(l * c) • U (R.symm (l • x))‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ = c * (‖fderiv ℝ U (R.symm (l • x))‖ * ((l * c) * ‖U (R.symm (l • x))‖)) := by
          rw [norm_smul, Real.norm_of_nonneg hlc]
      _ ≤ c * ((E * (1 + l * ‖x‖) ^ (-(2 * α))) *
            ((l * c) * (D * (1 + l * ‖x‖) ^ (-(2 * α - 1))))) := by
          gcongr
      _ = (c * c * l) * (E * D) *
            ((1 + l * ‖x‖) ^ (-(2 * α)) * (1 + l * ‖x‖) ^ (-(2 * α - 1))) := by ring
      _ = μ ^ (2 - 1 / (2 * α)) * (E * D) * (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by rw [e2, hexp]
  have bG : ‖gradientAt (fun y => k * P (Q (l • y))) x‖ ≤
      μ ^ (2 - 1 / (2 * α)) * (3 * D) * (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by
    refine (gradientAt_norm_le_sum _ x).trans ?_
    have qp := hp (Q (l • x))
    rw [hy'] at qp
    have hi : ∀ i : Fin 3, |fderiv ℝ (fun y => k * P (Q (l • y))) x (unitVector i)| ≤
        k * l * (D * (1 + l * ‖x‖) ^ (-(4 * α - 1))) := by
      intro i
      rw [rigidScale_scalar_fderiv_apply P hPd Q k l x, abs_mul, abs_of_pos hk0, mul_assoc]
      gcongr
      calc |fderiv ℝ P (Q (l • x)) (Q (l • unitVector i))|
          ≤ ‖fderiv ℝ P (Q (l • x))‖ * ‖Q (l • unitVector i)‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm _ _
        _ = l * ‖fderiv ℝ P (Q (l • x))‖ := by
            rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg hl0.le]
            simp [unitVector]
            ring
        _ ≤ l * (D * (1 + l * ‖x‖) ^ (-(4 * α - 1))) := by gcongr
    calc ∑ i : Fin 3, |fderiv ℝ (fun y => k * P (Q (l • y))) x (unitVector i)|
        ≤ ∑ _i : Fin 3, k * l * (D * (1 + l * ‖x‖) ^ (-(4 * α - 1))) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = μ ^ (2 - 1 / (2 * α)) * (3 * D) * (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← e3]
          push_cast
          ring
  have hM : 0 ≤ μ ^ (2 - 1 / (2 * α)) := by positivity
  calc _ ≤ ‖fractionalPowerAt α (fun y => c • R (U (R.symm (l • y)))) x‖
        + ‖advectionAt (fun y => c • R (U (R.symm (l • y)))) x‖
        + ‖gradientAt (fun y => k * P (Q (l • y))) x‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ μ ^ (2 - 1 / (2 * α)) * D * (1 + l * ‖x‖) ^ (-(4 * α - 1))
        + μ ^ (2 - 1 / (2 * α)) * (E * D) * (1 + l * ‖x‖) ^ (-(4 * α - 1))
        + μ ^ (2 - 1 / (2 * α)) * (3 * D) * (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by gcongr
    _ = μ ^ (2 - 1 / (2 * α)) * (D + E * D + 3 * D) * (1 + l * ‖x‖) ^ (-(4 * α - 1)) := by ring
    _ ≤ _ := by gcongr

end FracInternal

open FracInternal in
theorem selfSimilarTimeBound (_h1 : AxialRotationSpec) (h2 : SelfSimilarMomentum) :
    SelfSimilarTimeBound := by
  intro α hα1 hα2 a U P hU s₀ T hT
  obtain ⟨C0, hC0⟩ := hU.decay 0
  obtain ⟨C1, hC1⟩ := hU.decay 1
  have hT1 : 0 < 1 - T := by linarith
  have hα0 : 0 < α := by linarith
  have hA : ∀ y, ‖fractionalPowerAt α U y‖ ≤ max C0 0 * (1 + ‖y‖) ^ (-(4 * α - 1)) := by
    intro y
    have h := (hC0 y).2.2
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h0' : ∀ y, ‖U y‖ ≤ max C0 0 * (1 + ‖y‖) ^ (-(2 * α - 1)) := by
    intro y
    have h := (hC0 y).1
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hp' : ∀ y, ‖fderiv ℝ P y‖ ≤ max C0 0 * (1 + ‖y‖) ^ (-(4 * α - 1)) := by
    intro y
    have h := (hC0 y).2.1
    rw [show (0 : ℕ) + 1 = 1 from rfl, norm_iteratedFDeriv_one] at h
    simp only [Nat.cast_zero, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h1' : ∀ y, ‖fderiv ℝ U y‖ ≤ max C1 0 * (1 + ‖y‖) ^ (-(2 * α)) := by
    intro y
    have h := (hC1 y).1
    simp only [norm_iteratedFDeriv_one, Nat.cast_one] at h
    have e : -(2 * α - 1 + 1) = -(2 * α) := by ring
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hS : 0 ≤ max C0 0 + max C1 0 * max C0 0 + 3 * max C0 0 := by
    have := le_max_right C0 0
    have := le_max_right C1 0
    positivity
  have hg : 0 ≤ 2 - 1 / (2 * α) := by
    have : 1 / (2 * α) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  refine ⟨((1 - T)⁻¹) ^ (2 - 1 / (2 * α)) *
    (max C0 0 + max C1 0 * max C0 0 + 3 * max C0 0), ?_⟩
  intro t ht t' ht' x
  have hw : 0 ≤ (1 + ‖x‖) ^ (-(4 * α - 1)) := by positivity
  have key : ‖selfSimilarField α a U s₀ t x - selfSimilarField α a U s₀ t' x‖ ≤
      ((1 - T)⁻¹) ^ (2 - 1 / (2 * α)) * (max C0 0 + max C1 0 * max C0 0 + 3 * max C0 0) *
        (1 + ‖x‖) ^ (-(4 * α - 1)) * ‖t - t'‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => selfSimilarField α a U s₀ τ x)
      (fun τ hτ => (h2 α hα1 hα2 a U P hU s₀ τ (lt_of_le_of_lt hτ.2 hT) x).hasDerivWithinAt)
      ?_ (convex_Icc 0 T) ht' ht
    intro τ hτ
    have h3 : 0 < 1 - τ := by linarith [hτ.2]
    have hμ1 : 1 ≤ (1 - τ)⁻¹ := (one_le_inv₀ h3).2 (by linarith [hτ.1])
    have hμT : (1 - τ)⁻¹ ≤ (1 - T)⁻¹ := inv_anti₀ hT1 (by linarith [hτ.2])
    have hb := rigidScale_residual_bound α hα1 U P hU.smooth hU.smooth_pressure
      (axialRotation (-(a * (s₀ - Real.log (1 - τ)))))
      (axialRotation (a * (s₀ - Real.log (1 - τ)))) ((1 - τ)⁻¹) hμ1 (max C0 0) (max C1 0)
      (le_max_right _ _) (le_max_right _ _) hA h0' h1' hp' x
    refine le_trans hb ?_
    apply mul_le_mul_of_nonneg_right _ hw
    apply mul_le_mul_of_nonneg_right _ hS
    exact Real.rpow_le_rpow (by linarith) hμT hg
  calc ‖selfSimilarField α a U s₀ t x - selfSimilarField α a U s₀ t' x‖
      ≤ _ := key
    _ = _ := by
      rw [Real.norm_eq_abs]
      ring

end Breakdown
