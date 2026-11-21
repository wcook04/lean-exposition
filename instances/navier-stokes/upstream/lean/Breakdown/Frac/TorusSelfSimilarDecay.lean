import Breakdown.Frac.StTorusApprox
import Breakdown.Frac.StOperator

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracDecay.Internal

theorem scale_identity (μ g β K r : ℝ) (hμ : 0 < μ) (hr : 0 ≤ r) :
    μ ^ (-(g * β)) * (K * (1 + μ ^ (-g) * r) ^ (-β)) = K * (μ ^ g + r) ^ (-β) := by
  have h1 : 1 + μ ^ (-g) * r = μ ^ (-g) * (μ ^ g + r) := by
    rw [mul_add, ← rpow_add hμ, neg_add_cancel, rpow_zero]
  have hs : 0 < μ ^ g + r := add_pos_of_pos_of_nonneg (rpow_pos_of_pos hμ _) hr
  have h2 : (μ ^ (-g) * (μ ^ g + r)) ^ (-β) = μ ^ (g * β) * (μ ^ g + r) ^ (-β) := by
    rw [mul_rpow (rpow_nonneg hμ.le _) hs.le, ← rpow_mul hμ.le]
    congr 2
    ring
  have h3 : 0 < μ ^ (g * β) := rpow_pos_of_pos hμ _
  rw [h1, h2, rpow_neg hμ.le]
  field_simp

theorem norm_iteratedFDeriv_scaled {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : Space → F) (hh : ContDiff ℝ ∞ h) (l : ℝ) (j : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ j (fun y => h (l • (y - center))) x‖ =
      |l| ^ j * ‖iteratedFDeriv ℝ j h (l • (x - center))‖ := by
  have hj : ContDiff ℝ j h := hh.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDeriv_comp_sub (f := fun y => h (l • y)) j center x,
    iteratedFDeriv_comp_const_smul l hj]
  simp only [norm_smul, norm_pow, Real.norm_eq_abs]

theorem norm_iteratedFDeriv_push (R : Space ≃ₗᵢ[ℝ] Space) (U : Space → Space) (j : ℕ)
    (z : Space) :
    ‖iteratedFDeriv ℝ j (pushForward R U) z‖ = ‖iteratedFDeriv ℝ j U (R.symm z)‖ := by
  have e : pushForward R U = R ∘ (U ∘ R.symm) := rfl
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]

theorem grad_le (p : Space → ℝ) (x : Space) : ‖gradientAt p x‖ ≤ 3 * ‖fderiv ℝ p x‖ := by
  have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  unfold gradientAt
  calc ‖∑ i : Fin 3, fderiv ℝ p x (unitVector i) • unitVector i‖
      ≤ ∑ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ p x‖ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [norm_smul, hu, mul_one]
        calc ‖fderiv ℝ p x (unitVector i)‖ ≤ ‖fderiv ℝ p x‖ * ‖unitVector i‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ p x‖ := by rw [hu, mul_one]
    _ = 3 * ‖fderiv ℝ p x‖ := by simp

theorem adv_bound (f : Space → Space) (x : Space) (s K0 K1 α : ℝ) (hs : 0 < s)
    (h0 : ‖f x‖ ≤ K0 * s ^ (-(2 * α - 1))) (h1 : ‖fderiv ℝ f x‖ ≤ K1 * s ^ (-(2 * α))) :
    ‖advectionAt f x‖ ≤ K1 * K0 * s ^ (-(4 * α - 1)) := by
  have e : s ^ (-(4 * α - 1)) = s ^ (-(2 * α)) * s ^ (-(2 * α - 1)) := by
    rw [← rpow_add hs]
    congr 1
    ring
  calc ‖advectionAt f x‖ ≤ ‖fderiv ℝ f x‖ * ‖f x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (K1 * s ^ (-(2 * α))) * (K0 * s ^ (-(2 * α - 1))) :=
        mul_le_mul h1 h0 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = K1 * K0 * s ^ (-(4 * α - 1)) := by rw [e]; ring

theorem spatial_core (α : ℝ) (hα : 0 < α) (R : Space ≃ₗᵢ[ℝ] Space) (U : Space → Space)
    (hU : ContDiff ℝ ∞ U) (j : ℕ) (K : ℝ)
    (hK : ∀ y, ‖iteratedFDeriv ℝ j U y‖ ≤ K * (1 + ‖y‖) ^ (-(2 * α - 1 + j)))
    (μ : ℝ) (hμ : 0 < μ) (x : Space) :
    ‖iteratedFDeriv ℝ j (fun y => μ ^ (-(1 - 1 / (2 * α))) •
        pushForward R U (μ ^ (-(1 / (2 * α))) • (y - center))) x‖ ≤
      K * (μ ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1 + j)) := by
  have hg : 1 / (2 * α) * (2 * α) = 1 := by field_simp
  have hV : ContDiff ℝ ∞ (pushForward R U) := R.contDiff.comp (hU.comp R.symm.contDiff)
  have hW : ContDiff ℝ ∞ (fun y => pushForward R U (μ ^ (-(1 / (2 * α))) • (y - center))) :=
    hV.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hc : 0 < μ ^ (-(1 - 1 / (2 * α))) := rpow_pos_of_pos hμ _
  have hl : 0 < μ ^ (-(1 / (2 * α))) := rpow_pos_of_pos hμ _
  rw [iteratedFDeriv_const_smul_apply' (hW.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
    norm_smul, norm_iteratedFDeriv_scaled _ hV, norm_iteratedFDeriv_push, Real.norm_eq_abs,
    abs_of_pos hc, abs_of_pos hl]
  have hy : ‖R.symm (μ ^ (-(1 / (2 * α))) • (x - center))‖ =
      μ ^ (-(1 / (2 * α))) * ‖x - center‖ := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  have hpow : μ ^ (-(1 - 1 / (2 * α))) * (μ ^ (-(1 / (2 * α)))) ^ j =
      μ ^ (-(1 / (2 * α) * (2 * α - 1 + j))) := by
    rw [← rpow_natCast, ← rpow_mul hμ.le, ← rpow_add hμ]
    congr 1
    linear_combination hg
  calc μ ^ (-(1 - 1 / (2 * α))) * ((μ ^ (-(1 / (2 * α)))) ^ j *
        ‖iteratedFDeriv ℝ j U (R.symm (μ ^ (-(1 / (2 * α))) • (x - center)))‖)
      ≤ μ ^ (-(1 - 1 / (2 * α))) * ((μ ^ (-(1 / (2 * α)))) ^ j *
        (K * (1 + μ ^ (-(1 / (2 * α))) * ‖x - center‖) ^ (-(2 * α - 1 + j)))) := by
        rw [← hy]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK _) (pow_nonneg hl.le _))
          hc.le
    _ = (μ ^ (-(1 - 1 / (2 * α))) * (μ ^ (-(1 / (2 * α)))) ^ j) *
        (K * (1 + μ ^ (-(1 / (2 * α))) * ‖x - center‖) ^ (-(2 * α - 1 + j))) := by ring
    _ = K * (μ ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1 + j)) := by
        rw [hpow, scale_identity μ _ _ K _ hμ (norm_nonneg _)]

theorem frac_core (α : ℝ) (hC : CovarianceStatement) (R : Space ≃ₗᵢ[ℝ] Space)
    (U : Space → Space) (hU : ContDiff ℝ ∞ U) (c l : ℝ) (hl : 0 < l) (y : Space) :
    fractionalPowerAt α (fun x => c • pushForward R U (l • (x - center))) y =
      c • l ^ (2 * α) • R (fractionalPowerAt α U (R.symm (l • (y - center)))) := by
  have hV : ContDiff ℝ ∞ (pushForward R U) := R.contDiff.comp (hU.comp R.symm.contDiff)
  have hV2 : ContDiff ℝ 2 (pushForward R U) := hV.of_le (WithTop.coe_le_coe.mpr le_top)
  have hW2 : ContDiff ℝ 2 (fun z => pushForward R U (l • z)) :=
    hV2.comp (contDiff_const_smul l)
  have hX2 : ContDiff ℝ 2 (fun x => pushForward R U (l • (x - center))) :=
    hV2.comp ((contDiff_id.sub contDiff_const).const_smul l)
  have hU2 : ContDiff ℝ 2 U := hU.of_le (WithTop.coe_le_coe.mpr le_top)
  have e1 := (hC α _ hX2).2.1 c y
  have e2 := (hC α _ hW2).2.2.2 (-center) y
  have e3 := (hC α _ hV2).1 l hl (y - center)
  have e4 : fractionalPowerAt α (pushForward R U) (l • (y - center)) =
      R (fractionalPowerAt α U (R.symm (l • (y - center)))) :=
    (hC α U hU2).2.2.1 R (l • (y - center))
  have e2' : fractionalPowerAt α (fun x => pushForward R U (l • (x - center))) y =
      fractionalPowerAt α (fun z => pushForward R U (l • z)) (y - center) := by
    simpa only [← sub_eq_add_neg] using e2
  beta_reduce at e1 e3
  rw [e1, e2', e3, e4]

theorem frac_bound (α : ℝ) (hα : 0 < α) (hC : CovarianceStatement) (R : Space ≃ₗᵢ[ℝ] Space)
    (U : Space → Space) (hU : ContDiff ℝ ∞ U) (K : ℝ)
    (hK : ∀ y, ‖fractionalPowerAt α U y‖ ≤ K * (1 + ‖y‖) ^ (-(4 * α - 1)))
    (μ : ℝ) (hμ : 0 < μ) (x : Space) :
    ‖fractionalPowerAt α (fun y => μ ^ (-(1 - 1 / (2 * α))) •
        pushForward R U (μ ^ (-(1 / (2 * α))) • (y - center))) x‖ ≤
      K * (μ ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) := by
  have hg : 1 / (2 * α) * (2 * α) = 1 := by field_simp
  have hc : 0 < μ ^ (-(1 - 1 / (2 * α))) := rpow_pos_of_pos hμ _
  have hl : 0 < μ ^ (-(1 / (2 * α))) := rpow_pos_of_pos hμ _
  have hl2 : 0 < (μ ^ (-(1 / (2 * α)))) ^ (2 * α) := rpow_pos_of_pos hl _
  rw [frac_core α hC R U hU _ _ hl x, norm_smul, norm_smul, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc, abs_of_pos hl2]
  have hy : ‖R.symm (μ ^ (-(1 / (2 * α))) • (x - center))‖ =
      μ ^ (-(1 / (2 * α))) * ‖x - center‖ := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  have hpow : μ ^ (-(1 - 1 / (2 * α))) * (μ ^ (-(1 / (2 * α)))) ^ (2 * α) =
      μ ^ (-(1 / (2 * α) * (4 * α - 1))) := by
    rw [← rpow_mul hμ.le, ← rpow_add hμ]
    congr 1
    linear_combination hg
  calc μ ^ (-(1 - 1 / (2 * α))) * ((μ ^ (-(1 / (2 * α)))) ^ (2 * α) *
        ‖fractionalPowerAt α U (R.symm (μ ^ (-(1 / (2 * α))) • (x - center)))‖)
      ≤ μ ^ (-(1 - 1 / (2 * α))) * ((μ ^ (-(1 / (2 * α)))) ^ (2 * α) *
        (K * (1 + μ ^ (-(1 / (2 * α))) * ‖x - center‖) ^ (-(4 * α - 1)))) := by
        rw [← hy]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK _) hl2.le) hc.le
    _ = (μ ^ (-(1 - 1 / (2 * α))) * (μ ^ (-(1 / (2 * α)))) ^ (2 * α)) *
        (K * (1 + μ ^ (-(1 / (2 * α))) * ‖x - center‖) ^ (-(4 * α - 1))) := by ring
    _ = K * (μ ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) := by
        rw [hpow, scale_identity μ _ _ K _ hμ (norm_nonneg _)]

theorem pressure_bound (α : ℝ) (hα : 0 < α) (R : Space ≃ₗᵢ[ℝ] Space) (P : Space → ℝ)
    (hP : ContDiff ℝ ∞ P) (K : ℝ)
    (hK : ∀ y, ‖iteratedFDeriv ℝ 1 P y‖ ≤ K * (1 + ‖y‖) ^ (-(4 * α - 1)))
    (μ : ℝ) (hμ : 0 < μ) (x : Space) :
    ‖gradientAt (fun y => μ ^ (-(2 - 1 / α)) * P (R (μ ^ (-(1 / (2 * α))) • (y - center)))) x‖ ≤
      3 * (K * (μ ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1))) := by
  have hg : 1 / (2 * α) * (2 * α) = 1 := by field_simp
  have hQ : ContDiff ℝ ∞ (P ∘ R) := hP.comp R.contDiff
  have hW : ContDiff ℝ ∞ (fun y => (P ∘ R) (μ ^ (-(1 / (2 * α))) • (y - center))) :=
    hQ.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hc : 0 < μ ^ (-(2 - 1 / α)) := rpow_pos_of_pos hμ _
  have hl : 0 < μ ^ (-(1 / (2 * α))) := rpow_pos_of_pos hμ _
  have e : (fun y => μ ^ (-(2 - 1 / α)) * P (R (μ ^ (-(1 / (2 * α))) • (y - center)))) =
      fun y => μ ^ (-(2 - 1 / α)) • (P ∘ R) (μ ^ (-(1 / (2 * α))) • (y - center)) := rfl
  refine (grad_le _ x).trans ?_
  rw [← norm_iteratedFDeriv_one, e,
    iteratedFDeriv_const_smul_apply' (hW.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
    norm_smul, norm_iteratedFDeriv_scaled _ hQ, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right,
    Real.norm_eq_abs, abs_of_pos hc, abs_of_pos hl, pow_one]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hy : ‖R (μ ^ (-(1 / (2 * α))) • (x - center))‖ = μ ^ (-(1 / (2 * α))) * ‖x - center‖ := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  have hpow : μ ^ (-(2 - 1 / α)) * μ ^ (-(1 / (2 * α))) = μ ^ (-(1 / (2 * α) * (4 * α - 1))) := by
    rw [← rpow_add hμ]
    congr 1
    linear_combination 2 * hg
  calc μ ^ (-(2 - 1 / α)) * (μ ^ (-(1 / (2 * α))) *
        ‖iteratedFDeriv ℝ 1 P (R (μ ^ (-(1 / (2 * α))) • (x - center)))‖)
      ≤ μ ^ (-(2 - 1 / α)) * (μ ^ (-(1 / (2 * α))) *
        (K * (1 + μ ^ (-(1 / (2 * α))) * ‖x - center‖) ^ (-(4 * α - 1)))) := by
        rw [← hy]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK _) hl.le) hc.le
    _ = (μ ^ (-(2 - 1 / α)) * μ ^ (-(1 / (2 * α)))) *
        (K * (1 + μ ^ (-(1 / (2 * α))) * ‖x - center‖) ^ (-(4 * α - 1))) := by ring
    _ = K * (μ ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) := by
        rw [hpow, scale_identity μ _ _ K _ hμ (norm_nonneg _)]

end FracDecay.Internal

open FracDecay.Internal in
theorem fracSelfSimilarDecay_of (α : ℝ) (h1 : 1 < α) (_h2 : α < 5 / 4)
    (hS : FracSelfSimilarSolves α) (_hA : AxialRotationSpec) (hC : CovarianceStatement) :
    FracSelfSimilarDecay α := by
  intro a U P hU
  have hα : 0 < α := by linarith
  choose K hK using hU.decay
  have hB0 : 0 ≤ |K 0| + |K 1| + |K 2| + |K 3| := by positivity
  have hKB : ∀ j : ℕ, j ≤ 3 → |K j| ≤ |K 0| + |K 1| + |K 2| + |K 3| := by
    intro j hj
    interval_cases j <;>
      linarith [abs_nonneg (K 0), abs_nonneg (K 1), abs_nonneg (K 2), abs_nonneg (K 3)]
  generalize |K 0| + |K 1| + |K 2| + |K 3| = B at hB0 hKB
  refine ⟨B * B + 6 * B, ?_⟩
  intro T t hT _ _ ht x
  have hμ : 0 < T - t := sub_pos.mpr ht
  have hs : 0 < (T - t) ^ (1 / (2 * α)) + ‖x - center‖ :=
    add_pos_of_pos_of_nonneg (rpow_pos_of_pos hμ _) (norm_nonneg _)
  have hsp : ∀ j : ℕ, ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) x‖ ≤
      |K j| * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1 + j)) := by
    intro j
    refine spatial_core α hα _ U hU.smooth j (|K j|) (fun y => ?_) (T - t) hμ x
    exact (hK j y).1.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (rpow_nonneg (by positivity) _))
  have hX : 0 ≤ ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) := rpow_nonneg hs.le _
  have hadv : ‖advectionAt (fracSelfSimilar α a U T t) x‖ ≤
      |K 1| * |K 0| * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) := by
    refine adv_bound _ x _ _ _ α hs ?_ ?_
    · have := hsp 0
      rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at this
    · have := hsp 1
      rwa [norm_iteratedFDeriv_one, Nat.cast_one, sub_add_cancel] at this
  have hfrac : ‖fractionalPowerAt α (fracSelfSimilar α a U T t) x‖ ≤
      |K 0| * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) := by
    refine frac_bound α hα hC _ U hU.smooth (|K 0|) (fun y => ?_) (T - t) hμ x
    have := (hK 0 y).2.2
    rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (rpow_nonneg (by positivity) _))
  have hgrad : ‖gradientAt (fracSelfSimilarPressure α a P T t) x‖ ≤
      3 * (|K 0| * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1))) := by
    refine pressure_bound α hα _ P hU.smooth_pressure (|K 0|) (fun y => ?_) (T - t) hμ x
    have := (hK 0 y).2.1
    rw [zero_add, Nat.cast_zero, add_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (rpow_nonneg (by positivity) _))
  have hK0 := hKB 0 (by norm_num)
  have hK1 := hKB 1 (by norm_num)
  refine ⟨fun j hj => (hsp j).trans (mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hs.le _)), ?_, ?_⟩
  · nlinarith [hKB j hj]
  · obtain ⟨-, -, hsol⟩ := hS a U P hU T hT
    have hd := (hsol t ht x).2
    have hd' : deriv (fun τ => fracSelfSimilar α a U T τ x) t =
        -(advectionAt (fracSelfSimilar α a U T t) x + fractionalPowerAt α (fracSelfSimilar α a U T t) x
          + gradientAt (fracSelfSimilarPressure α a P T t) x) := by
      rw [eq_neg_iff_add_eq_zero, ← hd]
      abel
    rw [hd', norm_neg]
    refine (norm_add₃_le).trans ?_
    have h01 : |K 1| * |K 0| ≤ B * B :=
      mul_le_mul hK1 hK0 (abs_nonneg _) hB0
    nlinarith [mul_le_mul_of_nonneg_right h01 hX, mul_le_mul_of_nonneg_right hK0 hX]
  · nlinarith [mul_le_mul_of_nonneg_right hK0 hX]

end Breakdown.Periodic
