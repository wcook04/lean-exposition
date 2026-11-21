import Breakdown.Frac.TorusApproxCloseAux
import Breakdown.Frac.TorusApproxSizesAux
import Breakdown.Frac.PSlice

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracInternal.CutoffGradBound

variable {α a T t : ℝ} {U : Space → Space} {P : Space → ℝ}

theorem approx_contDiff (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) (ht : t < T) : ContDiff ℝ ∞ (fracApproxField α a U T t) := by
  have h := (hA a U P hU T hT).1
  rw [contDiff_iff_contDiffAt]
  intro x
  have hm : ((t, x) : ℝ × Space) ∈ Iio T ×ˢ (univ : Set Space) := ⟨ht, trivial⟩
  have h1 := h.contDiffAt ((isOpen_Iio.prod isOpen_univ).mem_nhds hm)
  have h2 : ContDiffAt ℝ ∞ (fun y : Space => ((t, y) : ℝ × Space)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact h1.comp x h2

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem sum_sq_le (L : Space →L[ℝ] Space) :
    ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 ≤ 3 * ‖L‖ ^ 2 := by
  have h : ∀ i : Fin 3, ‖L (unitVector i)‖ ^ 2 ≤ ‖L‖ ^ 2 := fun i => by
    have h1 : ‖L (unitVector i)‖ ≤ ‖L‖ := by
      have := L.le_opNorm (unitVector i)
      rwa [unit_norm, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖L‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖L‖ ^ 2 := by simp

theorem fderiv_dil_norm {F : Space → Space} (hF : Differentiable ℝ F) (c r : ℝ) (x₀ y : Space) :
    ‖fderiv ℝ (fun z => c • F (x₀ + r • z)) y‖ ≤ |c| * |r| * ‖fderiv ℝ F (x₀ + r • y)‖ := by
  have h1 : HasFDerivAt (fun z : Space => x₀ + r • z) (r • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id y).const_smul r).const_add x₀
  have h2 : HasFDerivAt (fun z => c • F (x₀ + r • z))
      (c • (fderiv ℝ F (x₀ + r • y)).comp (r • ContinuousLinearMap.id ℝ Space)) y :=
    ((hF (x₀ + r • y)).hasFDerivAt.comp y h1).const_smul c
  rw [h2.fderiv, norm_smul, Real.norm_eq_abs]
  have h3 : ‖(fderiv ℝ F (x₀ + r • y)).comp (r • ContinuousLinearMap.id ℝ Space)‖ ≤
      ‖fderiv ℝ F (x₀ + r • y)‖ * |r| := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg r) ContinuousLinearMap.norm_id_le
  calc |c| * ‖(fderiv ℝ F (x₀ + r • y)).comp (r • ContinuousLinearMap.id ℝ Space)‖
      ≤ |c| * (‖fderiv ℝ F (x₀ + r • y)‖ * |r|) := mul_le_mul_of_nonneg_left h3 (abs_nonneg c)
    _ = |c| * |r| * ‖fderiv ℝ F (x₀ + r • y)‖ := by ring

theorem dist_dil (r : ℝ) (hr : 0 ≤ r) (y : Space) : dist (center + r • y) center = r * ‖y‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr]

theorem core_eq (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) (ht : t < T) (y : Space)
    (hy : (T - t) ^ (1 / (2 * α)) * ‖y‖ ≤ centralRadius / 4) :
    fracCutAt α a U T t (T - t) y = rotatingSlice a U (similarityTime T t) y := by
  have hℓ : 0 < T - t := by linarith
  have hr0 : 0 ≤ (T - t) ^ (1 / (2 * α)) := Real.rpow_nonneg hℓ.le _
  have hd : dist (center + (T - t) ^ (1 / (2 * α)) • y) center ≤ centralRadius / 4 := by
    rw [dist_dil _ hr0]; exact hy
  unfold fracCutAt
  rw [(((hA a U P hU T hT).2.2 t ht _).2.2 hd)]
  unfold fracSelfSimilar
  rw [add_sub_cancel_left, smul_smul, smul_smul]
  have e1 : (T - t) ^ (-(1 / (2 * α))) * (T - t) ^ (1 / (2 * α)) = 1 := by
    rw [Real.rpow_neg hℓ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hℓ _).ne']
  have e2 : (T - t) ^ (1 - 1 / (2 * α)) * (T - t) ^ (-(1 - 1 / (2 * α))) = 1 := by
    rw [Real.rpow_neg hℓ.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hℓ _).ne']
  rw [e1, e2, one_smul, one_smul]

theorem outer_zero (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) (ht : t < T) (x : Space) (hx : centralRadius / 2 < dist x center) :
    fderiv ℝ (fracApproxField α a U T t) x = 0 := by
  have hev : fracApproxField α a U T t =ᶠ[𝓝 x] fun _ => (0 : Space) := by
    have ho : IsOpen {x' : Space | centralRadius / 2 < dist x' center} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    filter_upwards [ho.mem_nhds hx] with x' hx'
    exact (((hA a U P hU T hT).2.2 t ht x').2.1 (le_of_lt hx')).1
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

theorem tail_arith {B R ρ : ℝ} (hR : 0 ≤ R) (hρ : R ≤ ρ) :
    (B / (1 + ρ) ^ 2) ^ 2 ≤ B ^ 2 * (1 + R) ^ (-(1 / 2 : ℝ)) * (1 + ρ) ^ (-(7 / 2 : ℝ)) := by
  have hp : 0 < 1 + ρ := by linarith
  have hq : 0 < 1 + R := by linarith
  have e : (1 + ρ) ^ (-(7 / 2 : ℝ)) * (1 + ρ) ^ (-(1 / 2 : ℝ)) = ((1 + ρ) ^ 4)⁻¹ := by
    rw [← Real.rpow_add hp, show (-(7 / 2 : ℝ) + -(1 / 2 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hp.le, Real.rpow_natCast]
  have hm : (1 + ρ) ^ (-(1 / 2 : ℝ)) ≤ (1 + R) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hq (by linarith) (by norm_num)
  have h7 : 0 ≤ (1 + ρ) ^ (-(7 / 2 : ℝ)) := Real.rpow_nonneg hp.le _
  have hB : 0 ≤ B ^ 2 := sq_nonneg B
  calc (B / (1 + ρ) ^ 2) ^ 2 = B ^ 2 * ((1 + ρ) ^ (-(7 / 2 : ℝ)) * (1 + ρ) ^ (-(1 / 2 : ℝ))) := by
        rw [e, div_pow, ← pow_mul, div_eq_mul_inv]
    _ ≤ B ^ 2 * ((1 + ρ) ^ (-(7 / 2 : ℝ)) * (1 + R) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm h7) hB
    _ = B ^ 2 * (1 + R) ^ (-(1 / 2 : ℝ)) * (1 + ρ) ^ (-(7 / 2 : ℝ)) := by ring


theorem pointwise (hα : 1 < α) (hA : FracApproxFieldProperties α) (hU : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) (ht : t < T) {C G : ℝ} (hG0 : 0 ≤ G)
    (hC : ∀ s y, ‖fderiv ℝ (rotatingSlice a U s) y‖ ≤ C / (1 + ‖y‖) ^ 2)
    (hG : ∀ x, centralRadius / 4 ≤ dist x center → ‖fderiv ℝ (fracApproxField α a U T t) x‖ ≤ G)
    (hr1 : (T - t) ^ (1 / (2 * α)) ≤ 1 / 16) (y : Space) :
    ∑ i : Fin 3, ‖fderiv ℝ (rotatingSlice a U (similarityTime T t) - fracCutAt α a U T t (T - t)) y
        (unitVector i)‖ ^ 2 ≤
      3 * ((C + G) ^ 2 * (1 + 1 / (16 * (T - t) ^ (1 / (2 * α)))) ^ (-(1 / 2 : ℝ)) *
        (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) := by
  set r := (T - t) ^ (1 / (2 * α)) with hr
  have hℓ : 0 < T - t := by linarith
  have hα0 : 0 < α := by linarith
  have hr0 : 0 < r := Real.rpow_pos_of_pos hℓ _
  have hF := approx_contDiff hA hU hT ht
  have hFd : Differentiable ℝ (fracApproxField α a U T t) := hF.differentiable (by simp)
  have hSd : Differentiable ℝ (rotatingSlice a U (similarityTime T t)) :=
    (Breakdown.FracInternal.SliceBounds.slice_decayField hα hU _).1.differentiable (by simp)
  have hcut : fracCutAt α a U T t (T - t) =
      fun z => (T - t) ^ (1 - 1 / (2 * α)) • fracApproxField α a U T t (center + r • z) := rfl
  have hCd : Differentiable ℝ (fracCutAt α a U T t (T - t)) := by
    rw [hcut]
    fun_prop
  have hsum0 : 0 ≤ 3 * ((C + G) ^ 2 * (1 + 1 / (16 * r)) ^ (-(1 / 2 : ℝ)) *
      (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) := by positivity
  have hc4 : centralRadius / 4 = 1 / 16 := by rw [centralRadius]; norm_num
  have hc2 : centralRadius / 2 = 1 / 8 := by rw [centralRadius]; norm_num
  rcases lt_or_ge (r * ‖y‖) (centralRadius / 4) with hin | hout
  · have hev : (rotatingSlice a U (similarityTime T t) - fracCutAt α a U T t (T - t)) =ᶠ[𝓝 y]
        fun _ => (0 : Space) := by
      have ho : IsOpen {z : Space | r * ‖z‖ < centralRadius / 4} :=
        isOpen_lt (continuous_const.mul continuous_norm) continuous_const
      filter_upwards [ho.mem_nhds hin] with z hz
      rw [Pi.sub_apply, core_eq hA hU hT ht z (le_of_lt hz), sub_self]
    rw [hev.fderiv_eq, fderiv_const_apply]
    have h0 : ∀ i : Fin 3, ‖(0 : Space →L[ℝ] Space) (unitVector i)‖ ^ 2 = 0 := fun i => by simp
    simp only [h0, Finset.sum_const_zero]
    exact hsum0
  · have hR : 1 / (16 * r) ≤ ‖y‖ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hy1 : 1 ≤ ‖y‖ := by
      have : 1 ≤ 1 / (16 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    have hdiff : fderiv ℝ (rotatingSlice a U (similarityTime T t) - fracCutAt α a U T t (T - t)) y =
        fderiv ℝ (rotatingSlice a U (similarityTime T t)) y -
          fderiv ℝ (fracCutAt α a U T t (T - t)) y :=
      fderiv_sub (hSd y) (hCd y)
    have hcutn : ‖fderiv ℝ (fracCutAt α a U T t (T - t)) y‖ ≤ G / (1 + ‖y‖) ^ 2 := by
      rw [hcut]
      refine (fderiv_dil_norm hFd _ r center y).trans ?_
      have hcr : |(T - t) ^ (1 - 1 / (2 * α))| * |r| = T - t := by
        rw [abs_of_nonneg (Real.rpow_nonneg hℓ.le _), abs_of_nonneg hr0.le, hr, ← Real.rpow_add hℓ]
        norm_num
      rw [hcr]
      rcases lt_or_ge (centralRadius / 2) (r * ‖y‖) with hfar | hnear
      · rw [outer_zero hA hU hT ht _ (by rw [dist_dil _ hr0.le]; exact hfar), norm_zero, mul_zero]
        positivity
      · have hGx := hG _ (by rw [dist_dil _ hr0.le]; exact hout)
        have hℓr : T - t ≤ r ^ 2 := by
          have e : r ^ (2 * α) = T - t := by
            rw [hr, ← Real.rpow_mul hℓ.le, one_div_mul_cancel (by linarith : (2 * α) ≠ 0),
              Real.rpow_one]
          rw [← e, ← Real.rpow_two]
          exact Real.rpow_le_rpow_of_exponent_ge hr0 (by linarith) (by linarith)
        have h1 : r * (1 + ‖y‖) ≤ 1 := by nlinarith
        have h2 : (r * (1 + ‖y‖)) ^ 2 ≤ 1 := by nlinarith [mul_pos hr0 (by linarith : (0:ℝ) < 1 + ‖y‖)]
        calc (T - t) * ‖fderiv ℝ (fracApproxField α a U T t) (center + r • y)‖ ≤ r ^ 2 * G :=
              mul_le_mul hℓr hGx (norm_nonneg _) (sq_nonneg r)
          _ ≤ G / (1 + ‖y‖) ^ 2 := by
              rw [le_div_iff₀ (by positivity)]
              nlinarith [mul_le_mul_of_nonneg_left h2 hG0]
    have htot : ‖fderiv ℝ (rotatingSlice a U (similarityTime T t) - fracCutAt α a U T t (T - t)) y‖ ≤
        (C + G) / (1 + ‖y‖) ^ 2 := by
      rw [hdiff, add_div]
      exact (norm_sub_le _ _).trans (add_le_add (hC _ y) hcutn)
    refine (sum_sq_le _).trans ?_
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htot 2
    have htl := tail_arith (B := C + G) (by positivity : (0:ℝ) ≤ 1 / (16 * r)) hR
    linarith

end FracInternal.CutoffGradBound

open FracInternal.CutoffGradBound in
theorem fracCutoffGrad (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (hA : FracApproxFieldProperties α)
    (hSD : FracSelfSimilarDecay α) :
    ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P →
      ∀ η : ℝ, 0 < η → ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → T - t < ℓ₀ →
        gradEnergy (rotatingSlice a U (similarityTime T t) - fracCutAt α a U T t (T - t)) ≤ η := by
  intro a U P hU η hη
  obtain ⟨C₀, hC₀⟩ := Breakdown.FracInternal.SliceBounds.slice_bounds hα hU
  have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
  have hC : ∀ s y, ‖fderiv ℝ (rotatingSlice a U s) y‖ ≤ max C₀ 0 / (1 + ‖y‖) ^ 2 := fun s y =>
    (hC₀ s y).2.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨G₀, hG₀⟩ := fracShellGradientBound α hα hα2 hA hSD a U P hU
  have hG0 : 0 ≤ max G₀ 0 := le_max_right _ _
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ y : Space, (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) := ⟨_, rfl⟩
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  have hI0 : 0 ≤ I := hI ▸ integral_nonneg (fun y => by positivity)
  obtain ⟨K, hK⟩ : ∃ K, K = 3 * (max C₀ 0 + max G₀ 0) ^ 2 * I := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = η / (K + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨m, hm⟩ : ∃ m, m = min (1 / 16 : ℝ) (δ ^ 2 / 16) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact lt_min (by norm_num) (by positivity)
  refine ⟨m ^ (2 * α), Real.rpow_pos_of_pos hm0 _, fun T t hT hT1 ht0 htT hℓ₀ => ?_⟩
  have hℓ : 0 < T - t := by linarith
  have hr0 : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hℓ _
  have hrm : (T - t) ^ (1 / (2 * α)) < m := by
    have h := Real.rpow_lt_rpow hℓ.le hℓ₀ (by positivity : (0:ℝ) < 1 / (2 * α))
    rwa [← Real.rpow_mul hm0.le, mul_one_div_cancel (by linarith : (2 * α) ≠ 0), Real.rpow_one] at h
  have hr16 : (T - t) ^ (1 / (2 * α)) ≤ 1 / 16 := (hrm.trans_le (hm ▸ min_le_left _ _)).le
  have hrδ : (T - t) ^ (1 / (2 * α)) < δ ^ 2 / 16 := hrm.trans_le (hm ▸ min_le_right _ _)
  have hpt := fun y => pointwise hα hA hU hT htT hG0 hC
    (fun x hx => (hG₀ T t hT hT1 ht0 htT x hx).trans (le_max_left _ _)) hr16 y
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (1 + 1 / (16 * (T - t) ^ (1 / (2 * α)))) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hQ] at hpt
  have hmono : gradEnergy (rotatingSlice a U (similarityTime T t) - fracCutAt α a U T t (T - t)) ≤
      ∫ y : Space, 3 * ((max C₀ 0 + max G₀ 0) ^ 2 * Q * (1 + ‖y‖) ^ (-(7 / 2 : ℝ))) :=
    integral_mono_of_nonneg (Eventually.of_forall fun y => Finset.sum_nonneg fun i _ => sq_nonneg _)
      ((hint.const_mul _).const_mul _) (Eventually.of_forall hpt)
  rw [integral_const_mul, integral_const_mul, ← hI] at hmono
  have hQδ : Q ≤ δ := by
    have hx : (δ ^ 2)⁻¹ ≤ 1 + 1 / (16 * (T - t) ^ (1 / (2 * α))) := by
      have : 1 / δ ^ 2 ≤ 1 / (16 * (T - t) ^ (1 / (2 * α))) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      rw [← one_div]
      linarith
    have e : ((δ ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = δ := by
      rw [Real.rpow_neg (inv_nonneg.2 (sq_nonneg _)), Real.inv_rpow (sq_nonneg _), inv_inv,
        ← Real.sqrt_eq_rpow, Real.sqrt_sq hδ0.le]
    rw [hQ, ← e]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hx (by norm_num)
  have hKδ : K * δ ≤ η := by
    rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have e3 : 3 * ((max C₀ 0 + max G₀ 0) ^ 2 * Q * I) = K * Q := by rw [hK]; ring
  rw [e3] at hmono
  exact hmono.trans ((mul_le_mul_of_nonneg_left hQδ hK0).trans hKδ)

end Breakdown.Periodic
