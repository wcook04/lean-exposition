import Breakdown.Frac.StTorusStepApprox
import Breakdown.Frac.StTorusShell
import Breakdown.Frac.TorusResidualOuterBound
import Breakdown.Torus.ApproxSizes
import Breakdown.Torus.ApproxResidual
import Breakdown.Torus.Transplant
import Breakdown.Torus.TestLift
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusApproxDatum.Internal

theorem periodize_wrap {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x : Space) :
    latticePeriodize f x = f (wrap x) := by
  have hw : wrap x = x + freq (fun i => -round (x i - 1 / 2)) := by
    ext i
    rw [Transplant.Internal.wrap_apply, PiLp.add_apply, Transplant.Internal.freq_apply']
    push_cast
    ring
  rw [hw]
  unfold latticePeriodize
  refine tsum_eq_single (fun i => -round (x i - 1 / 2)) fun j hj => ?_
  by_contra h
  apply hj
  funext i
  have a1 := (ApproxResidual.Internal.coord_le_dist _ _ i).trans (hf _ h)
  rw [PiLp.add_apply, Transplant.Internal.freq_apply', ApproxResidual.Internal.center_apply] at a1
  have a3 := abs_sub_round (x i - 1 / 2)
  rw [abs_le] at a1 a3
  have key : |((j i + round (x i - 1 / 2) : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a3.1, a3.2]
  have h' : |j i + round (x i - 1 / 2)| < 1 := by exact_mod_cast key
  have := abs_lt.mp h'
  omega

theorem slice_zero (a : ℝ) (U : Space → Space) : rotatingSlice a U 0 = U := by
  have h0 : ∀ y, axialRotation 0 y = y := by
    intro y
    unfold axialRotation
    split_ifs with h
    · rw [h.choose_spec]
      ext i
      fin_cases i <;> simp [axialRotationFormula]
    · rfl
  funext y
  have h1 : (axialRotation 0).symm y = y := by
    have := h0 ((axialRotation 0).symm y)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [rotatingSlice, pushForward, mul_zero, neg_zero]
  rw [h1, h0]

theorem rpow_le_of_mul {r X p : ℝ} (hr : 0 < r) (hX : 0 < X) (hrX : r * X ≤ 1) (hp : 0 ≤ p) :
    X ^ p ≤ r ^ (-p) := by
  have h1 : (r * X) ^ p ≤ 1 := Real.rpow_le_one (by positivity) hrX hp
  rw [Real.mul_rpow hr.le hX.le] at h1
  rw [Real.rpow_neg hr.le, inv_eq_one_div, le_div_iff₀ (Real.rpow_pos_of_pos hr p)]
  linarith [mul_comm (r ^ p) (X ^ p)]

theorem rpow_neg_le_of_mul {r X p : ℝ} (hr : 0 < r) (hX : 0 < X) (hrX : 1 ≤ 16 * r * X) (hp : 0 ≤ p) :
    X ^ (-p) ≤ 16 ^ p * r ^ p := by
  have h1 : 1 ≤ (16 * r * X) ^ p := Real.one_le_rpow hrX hp
  rw [Real.mul_rpow (by positivity) hX.le, Real.mul_rpow (by norm_num) hr.le] at h1
  rw [Real.rpow_neg hX.le, inv_eq_one_div, div_le_iff₀ (Real.rpow_pos_of_pos hX p)]
  exact h1

theorem sq_rpow {X p : ℝ} (hX : 0 < X) : (X ^ p) ^ 2 = X ^ (2 * p) := by
  rw [mul_comm, Real.rpow_mul hX.le, Real.rpow_two]

theorem tail_bound {α r X : ℝ} (hα : 1 < α) (hr : 0 < r) (hX : 0 < X) (hrX : 1 ≤ 16 * r * X) :
    (X ^ (-(2 * α))) ^ 2 ≤ 16 ^ (2 * α - 3 / 2) * r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2)) := by
  rw [sq_rpow hX, show 2 * -(2 * α) = -(2 * α - 3 / 2) + -(2 * α + 3 / 2) by ring,
    Real.rpow_add hX]
  exact mul_le_mul_of_nonneg_right (rpow_neg_le_of_mul hr hX hrX (by linarith))
    (Real.rpow_nonneg hX.le _)

theorem inner_bound {α r X : ℝ} (hα2 : α < 5 / 4) (hr : 0 < r) (hX : 0 < X) (hrX : r * X ≤ 1) :
    r ^ 2 * (X ^ (-(2 * α - 1))) ^ 2 ≤ r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2)) := by
  rw [sq_rpow hX, show 2 * -(2 * α - 1) = (7 / 2 - 2 * α) + -(2 * α + 3 / 2) by ring,
    Real.rpow_add hX, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hX.le _)
  have h1 := rpow_le_of_mul hr hX hrX (p := 7 / 2 - 2 * α) (by linarith)
  have e : r ^ (2 * α - 3 / 2) = r ^ (2 : ℝ) * r ^ (-(7 / 2 - 2 * α)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [e, Real.rpow_two]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem shell_bound {α r X : ℝ} (hα : 1 < α) (hr : 0 < r) (hX : 0 < X) (hrX : r * X ≤ 1) :
    r ^ (4 * α) ≤ r ^ (2 * α - 3 / 2) * X ^ (-(2 * α + 3 / 2)) := by
  rw [show 4 * α = (2 * α - 3 / 2) + (2 * α + 3 / 2) by ring, Real.rpow_add hr]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr.le _)
  have h1 := rpow_le_of_mul hX hr (by linarith [mul_comm r X]) (p := 2 * α + 3 / 2) (by linarith)
  exact h1


def scaledAt (s r : ℝ) (F : Space → Space) (y : Space) : Space := s • F (center + r • y)

theorem hasFDerivAt_scaledAt {F : Space → Space} (hF : Differentiable ℝ F) (s r : ℝ) (y : Space) :
    HasFDerivAt (scaledAt s r F) ((s * r) • fderiv ℝ F (center + r • y)) y := by
  have h1 : HasFDerivAt (fun y : Space => center + r • y) (r • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul r).const_add center
  have h2 := ((hF _).hasFDerivAt.comp y h1).const_smul s
  have e : (s * r) • fderiv ℝ F (center + r • y) =
      s • ((fderiv ℝ F (center + r • y)).comp (r • ContinuousLinearMap.id ℝ Space)) := by
    ext v
    simp [smul_smul]
  rw [e]
  exact h2

theorem fderiv_scaledAt {F : Space → Space} (hF : Differentiable ℝ F) (s r : ℝ) (y : Space) :
    fderiv ℝ (scaledAt s r F) y = (s * r) • fderiv ℝ F (center + r • y) :=
  (hasFDerivAt_scaledAt hF s r y).fderiv

theorem contDiff_scaledAt {F : Space → Space} (hF : ContDiff ℝ ∞ F) (s r : ℝ) :
    ContDiff ℝ ∞ (scaledAt s r F) := by
  unfold scaledAt
  exact (hF.comp (contDiff_const.add (contDiff_id.const_smul r))).const_smul s

theorem div_scaledAt {F : Space → Space} (hF : Differentiable ℝ F)
    (hdiv : ∀ x, divergenceAt F x = 0) (s r : ℝ) (y : Space) :
    divergenceAt (scaledAt s r F) y = 0 := by
  have h := hdiv (center + r • y)
  simp only [divergenceAt] at h ⊢
  simp only [fderiv_scaledAt hF, smul_apply, PiLp.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, h, mul_zero]

theorem dist_scaled {r : ℝ} (hr : 0 ≤ r) (y : Space) : dist (center + r • y) center = r * ‖y‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

theorem tsupport_scaledAt {F : Space → Space} {s r : ℝ} (hr : 0 < r)
    (hF : ∀ x, 1 / 8 ≤ dist x center → F x = 0) :
    tsupport (scaledAt s r F) ⊆ Metric.closedBall 0 (1 / (8 * r)) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  rw [Function.mem_support] at hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  have hlt' := lt_of_not_ge hlt
  apply hy
  have hd : 1 / 8 ≤ dist (center + r • y) center := by
    rw [dist_scaled hr.le]
    rw [div_lt_iff₀ (by positivity)] at hlt'
    nlinarith
  simp [scaledAt, hF _ hd]

open FracOuterBoundInternal Cutoff.Internal in
theorem shell_derivs (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hD : FracSelfSimilarDecay α)
    (hF : FracApproxFieldProperties α) (a : ℝ) (U : Space → Space) (P : Space → ℝ)
    (hU : IsRotatingProfile α a 1 U P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ y : Space,
      centralRadius / 4 ≤ dist y center → ∀ j ≤ 3,
        ‖iteratedFDeriv ℝ j (fracApproxField α a U T t) y‖ ≤ K := by
  obtain ⟨C, hC⟩ := hD a U P hU
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; exact le_max_right _ _
  have hCC : C ≤ C' := by rw [hC']; exact le_max_left _ _
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (1 / 16 : ℝ) ^ (-(5 : ℝ)) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact Real.rpow_nonneg (by norm_num) _
  obtain ⟨KA, hKA0, hKA⟩ := potential_bound α h1 h2 hD a U P hU
  obtain ⟨Kc, hKc0, hKc⟩ := bounded_upto3 ApproxField.Internal.contDiff_centralCut
    (centralBump.hasCompactSupport : HasCompactSupport centralCut)
  obtain ⟨Kd, hKd0, hKd⟩ := bounded_upto3 ApproxField.Internal.contDiff_gradient_centralCut
    gradient_support
  have hB0 : 0 ≤ ‖crossBilinear‖ := norm_nonneg _
  refine ⟨8 * (Kc * (C' * N)) + ‖crossBilinear‖ * (8 * (Kd * KA)), by positivity, ?_⟩
  intro T t hT hT1 ht0 htT y hy j hj
  have hμ : 0 < T - t := by linarith
  have hμ1 : T - t ≤ 1 := by linarith
  have hg : ContDiff ℝ ∞ (fracSelfSimilar α a U T t) := selfSimilar_contDiff hU.smooth T t
  have hA : ContDiff ℝ ∞ (homotopyPotential center (fracSelfSimilar α a U T t)) := by
    rw [homotopyPotential_eq]
    exact contDiff_integral_unit_infty _ (contDiff_potentialIntegrand hg)
  have hform : fracApproxField α a U T t = fun w => centralCut w • fracSelfSimilar α a U T t w +
      crossBilinear (gradientAt centralCut w) (homotopyPotential center (fracSelfSimilar α a U T t) w) :=
    rfl
  have hμg : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  have hgb : ∀ w : Space, 1 / 16 ≤ dist w center → ∀ j ≤ 3,
      ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) w‖ ≤ C' * N := by
    intro w hw j hj
    have hb := (hC T t hT hT1 ht0 htT w).1 j hj
    have hwc : ‖w - center‖ = dist w center := (dist_eq_norm w center).symm
    rw [hwc] at hb
    have hej : 0 ≤ 2 * α - 1 + (j : ℝ) := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hfar := far_le (μ := (T - t) ^ (1 / (2 * α))) (σ := dist w center) (by linarith) hμg.le
      le_rfl hej
    have hcst := const_le (ρ := dist w center) (e := 2 * α - 1 + (j : ℝ)) hw hej
      (by have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
          linarith)
    have hX : 0 ≤ ((T - t) ^ (1 / (2 * α)) + dist w center) ^ (-(2 * α - 1 + (j : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    calc ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) w‖
        ≤ C * ((T - t) ^ (1 / (2 * α)) + dist w center) ^ (-(2 * α - 1 + (j : ℝ))) := hb
      _ ≤ C' * ((T - t) ^ (1 / (2 * α)) + dist w center) ^ (-(2 * α - 1 + (j : ℝ))) :=
          mul_le_mul_of_nonneg_right hCC hX
      _ ≤ C' * N := by
          rw [hN]
          exact mul_le_mul_of_nonneg_left (hfar.trans hcst) hC'0
  have hs1 : ContDiff ℝ ∞ (fun w => centralCut w • fracSelfSimilar α a U T t w) :=
    ApproxField.Internal.contDiff_centralCut.smul hg
  have hs2 : ContDiff ℝ ∞ (fun w => crossBilinear (gradientAt centralCut w)
      (homotopyPotential center (fracSelfSimilar α a U T t) w)) :=
    (crossBilinear.contDiff.comp ApproxField.Internal.contDiff_gradient_centralCut).clm_apply hA
  have hy1 : 1 / 16 ≤ dist y center := by norm_num [centralRadius] at hy; linarith
  rcases le_total (dist y center) (1 / 8) with hle | hge
  · rw [hform]
    show ‖iteratedFDeriv ℝ j ((fun w => centralCut w • fracSelfSimilar α a U T t w) +
      (fun w => crossBilinear (gradientAt centralCut w)
        (homotopyPotential center (fracSelfSimilar α a U T t) w))) y‖ ≤ _
    rw [iteratedFDeriv_add_apply (hs1.contDiffAt.of_le (nat_le_infty j))
      (hs2.contDiffAt.of_le (nat_le_infty j))]
    have hsm := norm_iteratedFDeriv_smul_le ApproxField.Internal.contDiff_centralCut hg y
      (nat_le_infty j)
    have hsum1 := binom_sum_le3 (a := fun i => ‖iteratedFDeriv ℝ i centralCut y‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) y‖)
      (fun i hi => ⟨norm_nonneg _, hKc i hi y⟩) (fun i hi => ⟨norm_nonneg _, hgb y hy1 i hi⟩)
      hj
    have hbl := crossBilinear.norm_iteratedFDeriv_le_of_bilinear
      ApproxField.Internal.contDiff_gradient_centralCut hA y (nat_le_infty j)
    have hsum2 := binom_sum_le3 (a := fun i => ‖iteratedFDeriv ℝ i (gradientAt centralCut) y‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (homotopyPotential center (fracSelfSimilar α a U T t)) y‖)
      (fun i hi => ⟨norm_nonneg _, hKd i hi y⟩)
      (fun i hi => ⟨norm_nonneg _, hKA T t hT hT1 ht0 htT y hy1 hle i hi⟩) hj
    have hb2 := mul_le_mul_of_nonneg_left hsum2 hB0
    refine (norm_add_le _ _).trans ?_
    have : 0 ≤ C' + ‖crossBilinear‖ * Kd * KA := by positivity
    linarith
  · rw [iteratedFDeriv_eq_zero_outer (hform ▸ (hs1.add hs2)) (fun w hw => ((hF a U P hU T hT).2.2 t htT w).2.1 hw |>.1)
      j (by norm_num [centralRadius]; linarith), norm_zero]
    positivity

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by simp [unitVector]

theorem grad_point {α r Kf C1 : ℝ} (hα : 1 < α) (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    {U h : Space → Space} (hU : Differentiable ℝ U) (hh : Differentiable ℝ h)
    (hin : ∀ y, r * ‖y‖ < 1 / 16 → h =ᶠ[𝓝 y] U)
    (hout : ∀ y, 1 / 8 < r * ‖y‖ → fderiv ℝ h y = 0)
    (hshell : ∀ y, 1 / 16 ≤ r * ‖y‖ → ‖fderiv ℝ h y‖ ≤ r ^ (2 * α) * Kf)
    (hC1 : ∀ y, ‖fderiv ℝ U y‖ ≤ C1 * (1 + ‖y‖) ^ (-(2 * α))) (y : Space) :
    ∑ i : Fin 3, ‖fderiv ℝ (U - h) y (unitVector i)‖ ^ 2 ≤
      6 * (C1 ^ 2 * 16 ^ (2 * α - 3 / 2) + Kf ^ 2) * r ^ (2 * α - 3 / 2) *
        (1 + ‖y‖) ^ (-(2 * α + 3 / 2)) := by
  have hX : 0 < 1 + ‖y‖ := by positivity
  have hw : 0 ≤ (1 + ‖y‖) ^ (-(2 * α + 3 / 2)) := Real.rpow_nonneg hX.le _
  have hρ : 0 ≤ r ^ (2 * α - 3 / 2) := Real.rpow_nonneg hr.le _
  have h16 : 0 ≤ (16 : ℝ) ^ (2 * α - 3 / 2) := Real.rpow_nonneg (by norm_num) _
  have hfd : fderiv ℝ (U - h) y = fderiv ℝ U y - fderiv ℝ h y :=
    ((hU y).hasFDerivAt.sub (hh y).hasFDerivAt).fderiv
  by_cases hy : r * ‖y‖ < 1 / 16
  · rw [hfd, (hin y hy).fderiv_eq, sub_self]
    simp only [zero_apply, norm_zero]
    norm_num
    positivity
  · have hy' : 1 / 16 ≤ r * ‖y‖ := le_of_not_gt hy
    set D := fderiv ℝ (U - h) y
    have hsum : ∑ i : Fin 3, ‖D (unitVector i)‖ ^ 2 ≤ 3 * ‖D‖ ^ 2 := by
      have hi : ∀ i : Fin 3, ‖D (unitVector i)‖ ^ 2 ≤ ‖D‖ ^ 2 := by
        intro i
        have := D.le_opNorm (unitVector i)
        rw [unit_norm, mul_one] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      calc ∑ i : Fin 3, ‖D (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖D‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => hi i
        _ = 3 * ‖D‖ ^ 2 := by simp
    have hD : ‖D‖ ^ 2 ≤ 2 * ‖fderiv ℝ U y‖ ^ 2 + 2 * ‖fderiv ℝ h y‖ ^ 2 := by
      have h1 : ‖D‖ ≤ ‖fderiv ℝ U y‖ + ‖fderiv ℝ h y‖ := by rw [hfd]; exact norm_sub_le _ _
      nlinarith [norm_nonneg D, norm_nonneg (fderiv ℝ U y), norm_nonneg (fderiv ℝ h y),
        sq_nonneg (‖fderiv ℝ U y‖ - ‖fderiv ℝ h y‖)]
    have hUb : ‖fderiv ℝ U y‖ ^ 2 ≤
        C1 ^ 2 * (16 ^ (2 * α - 3 / 2) * r ^ (2 * α - 3 / 2) * (1 + ‖y‖) ^ (-(2 * α + 3 / 2))) := by
      have h1 : ‖fderiv ℝ U y‖ ^ 2 ≤ (C1 * (1 + ‖y‖) ^ (-(2 * α))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hC1 y) 2
      have h2 := tail_bound hα hr hX (by nlinarith [norm_nonneg y])
      rw [mul_pow] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
    have hhb : ‖fderiv ℝ h y‖ ^ 2 ≤ Kf ^ 2 * (r ^ (2 * α - 3 / 2) * (1 + ‖y‖) ^ (-(2 * α + 3 / 2))) := by
      by_cases ho : 1 / 8 < r * ‖y‖
      · rw [hout y ho, norm_zero]
        norm_num
        positivity
      · have ho' : r * ‖y‖ ≤ 1 / 8 := le_of_not_gt ho
        have h1 : ‖fderiv ℝ h y‖ ^ 2 ≤ (r ^ (2 * α) * Kf) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hshell y hy') 2
        rw [mul_pow, sq_rpow hr, show 2 * (2 * α) = 4 * α by ring] at h1
        have h2 := shell_bound hα hr hX (by nlinarith)
        nlinarith [sq_nonneg Kf]
    nlinarith

theorem mass_point {α r Kf C0 : ℝ} (hα : 1 < α) (hα2 : α < 5 / 4) (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    {U h : Space → Space} (hin : ∀ y, r * ‖y‖ ≤ 1 / 16 → h y = U y)
    (hout : ∀ y, 1 / 8 < r * ‖y‖ → h y = 0)
    (hshell : ∀ y, 1 / 16 ≤ r * ‖y‖ → ‖h y‖ ≤ r ^ (2 * α - 1) * Kf)
    (hC0 : ∀ y, ‖U y‖ ≤ C0 * (1 + ‖y‖) ^ (-(2 * α - 1))) (y : Space) :
    r ^ 2 * ‖h y‖ ^ 2 ≤ (C0 ^ 2 + Kf ^ 2) * r ^ (2 * α - 3 / 2) * (1 + ‖y‖) ^ (-(2 * α + 3 / 2)) := by
  have hX : 0 < 1 + ‖y‖ := by positivity
  have hw : 0 ≤ (1 + ‖y‖) ^ (-(2 * α + 3 / 2)) := Real.rpow_nonneg hX.le _
  have hρ : 0 ≤ r ^ (2 * α - 3 / 2) := Real.rpow_nonneg hr.le _
  have hρw := mul_nonneg hρ hw
  by_cases h1 : r * ‖y‖ ≤ 1 / 16
  · rw [hin y h1]
    have a1 : ‖U y‖ ^ 2 ≤ C0 ^ 2 * ((1 + ‖y‖) ^ (-(2 * α - 1))) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC0 y) 2
    have a2 := inner_bound hα2 hr hX (by nlinarith)
    have a3 : r ^ 2 * ‖U y‖ ^ 2 ≤ C0 ^ 2 * (r ^ 2 * ((1 + ‖y‖) ^ (-(2 * α - 1))) ^ 2) := by
      nlinarith [sq_nonneg r]
    nlinarith [sq_nonneg C0, sq_nonneg Kf]
  · have h1' : 1 / 16 ≤ r * ‖y‖ := (lt_of_not_ge h1).le
    by_cases h2 : 1 / 8 < r * ‖y‖
    · rw [hout y h2, norm_zero]
      norm_num
      positivity
    · have h2' : r * ‖y‖ ≤ 1 / 8 := le_of_not_gt h2
      have a1 : ‖h y‖ ^ 2 ≤ (r ^ (2 * α - 1) * Kf) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hshell y h1') 2
      rw [mul_pow, sq_rpow hr] at a1
      have e : r ^ 2 * r ^ (2 * (2 * α - 1)) = r ^ (4 * α) := by
        rw [← Real.rpow_two, ← Real.rpow_add hr]
        congr 1
        ring
      have a2 := shell_bound hα hr hX (by nlinarith)
      have a3 : r ^ 2 * ‖h y‖ ^ 2 ≤ r ^ 2 * (r ^ (2 * (2 * α - 1)) * Kf ^ 2) :=
        mul_le_mul_of_nonneg_left a1 (sq_nonneg r)
      rw [← mul_assoc, e] at a3
      nlinarith [sq_nonneg C0, sq_nonneg Kf]

theorem inner_eq {α a : ℝ} {U : Space → Space} {P : Space → ℝ} (hα : 1 < α)
    (hA : FracApproxFieldProperties α) (hR : IsRotatingProfile α a 1 U P) {T r : ℝ} (hT : 0 < T)
    (hrT : r = T ^ (1 / (2 * α))) (y : Space) (hy : r * ‖y‖ ≤ 1 / 16) :
    scaledAt (r ^ (2 * α - 1)) r (fracApproxField α a U T 0) y = U y := by
  subst hrT
  have hr := Real.rpow_pos_of_pos hT (1 / (2 * α))
  have hd : dist (center + T ^ (1 / (2 * α)) • y) center ≤ centralRadius / 4 := by
    rw [dist_scaled hr.le, show centralRadius / 4 = 1 / 16 by norm_num [centralRadius]]
    exact hy
  have hα0 : α ≠ 0 := by positivity
  have e1 : T ^ (-(1 / (2 * α))) * T ^ (1 / (2 * α)) = 1 := by
    rw [← Real.rpow_add hT, neg_add_cancel, Real.rpow_zero]
  have e2 : (T ^ (1 / (2 * α))) ^ (2 * α - 1) * T ^ (-(1 - 1 / (2 * α))) = 1 := by
    rw [← Real.rpow_mul hT.le, ← Real.rpow_add hT]
    rw [show 1 / (2 * α) * (2 * α - 1) + -(1 - 1 / (2 * α)) = 0 by field_simp; ring, Real.rpow_zero]
  have hs : similarityTime T 0 = 0 := by simp [similarityTime, hT.ne']
  rw [scaledAt, ((hA a U P hR T hT).2.2 0 hT _).2.2 hd]
  simp only [fracSelfSimilar, sub_zero, add_sub_cancel_left, hs, slice_zero, smul_smul, e1, one_smul, e2]

theorem integral_weight_le {α K : ℝ} (hα : 1 < α) {F : Space → ℝ} (hF0 : ∀ y, 0 ≤ F y)
    (hF : ∀ y, F y ≤ K * (1 + ‖y‖) ^ (-(2 * α + 3 / 2))) :
    ∫ y, F y ≤ K * ∫ y : Space, (1 + ‖y‖) ^ (-(2 * α + 3 / 2)) := by
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(2 * α + 3 / 2))) :=
    integrable_one_add_norm (by simp; linarith)
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall hF0) (hint.const_mul K) (Eventually.of_forall hF)

theorem eventually_small {α c p ε : ℝ} (hα : 0 < α) (hp : 0 < p) (hε : 0 < ε) :
    ∀ᶠ T in 𝓝[>] (0 : ℝ), c * (T ^ (1 / (2 * α))) ^ p < ε := by
  have h1 : Tendsto (fun T : ℝ => T ^ (1 / (2 * α))) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / (2 * α)) (Or.inr (by positivity))).tendsto
    rw [Real.zero_rpow (by positivity)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun T : ℝ => c * (T ^ (1 / (2 * α))) ^ p) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp h1).const_mul c
    rwa [Real.zero_rpow hp.ne', mul_zero] at this
  exact h2.eventually (eventually_lt_nhds hε)

end TorusApproxDatum.Internal

set_option maxHeartbeats 400000 in
open TorusApproxDatum.Internal FracOuterBoundInternal ApproxSizes.Internal in
theorem fracDatumClose (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (hN : TransplantNorm)
    (hS : TransplantSmooth) (hA : FracApproxFieldProperties α) (hL : FracApproxLinks α) (hV : ToVAdd)
    (hSD : FracSelfSimilarDecay α) : FracDatumClose α := by
  intro a U P lam b δ ψ₀ hR hl hl1 hψ hsupp hb hδ
  obtain ⟨hE, hEL⟩ := Freq.embedNormLinear_holds
  obtain ⟨Kf, hKf0, hKf⟩ := shell_derivs α hα hα2 hSD hA a U P hR
  obtain ⟨C0, hC0⟩ := hR.decay 0
  obtain ⟨C1, hC1⟩ := hR.decay 1
  have hU0 : ∀ y, ‖U y‖ ≤ max C0 0 * (1 + ‖y‖) ^ (-(2 * α - 1)) := by
    intro y
    have h := (hC0 y).1
    rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  have hU1 : ∀ y, ‖fderiv ℝ U y‖ ≤ max C1 0 * (1 + ‖y‖) ^ (-(2 * α)) := by
    intro y
    have h := (hC1 y).1
    rw [norm_iteratedFDeriv_one, Nat.cast_one, show 2 * α - 1 + 1 = 2 * α by ring] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  have hUdec : IsDecayField U := by
    refine ⟨hR.smooth, hR.div, max C0 0 + max C1 0, fun y => ⟨?_, ?_⟩⟩
    · have h1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      have e : (1 + ‖y‖) ^ (-(2 * α - 1)) ≤ (1 + ‖y‖) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      rw [Real.rpow_neg_one] at e
      rw [div_eq_mul_inv]
      calc ‖U y‖ ≤ max C0 0 * (1 + ‖y‖)⁻¹ :=
            (hU0 y).trans (mul_le_mul_of_nonneg_left e (le_max_right _ _))
        _ ≤ (max C0 0 + max C1 0) * (1 + ‖y‖)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith [le_max_right C1 0]) (by positivity)
    · have h1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      have e : (1 + ‖y‖) ^ (-(2 * α)) ≤ (1 + ‖y‖) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      have e2 : (1 + ‖y‖) ^ (-2 : ℝ) = ((1 + ‖y‖) ^ 2)⁻¹ := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two]
      rw [e2] at e
      rw [div_eq_mul_inv]
      calc ‖fderiv ℝ U y‖ ≤ max C1 0 * ((1 + ‖y‖) ^ 2)⁻¹ :=
            (hU1 y).trans (mul_le_mul_of_nonneg_left e (le_max_right _ _))
        _ ≤ (max C0 0 + max C1 0) * ((1 + ‖y‖) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith [le_max_right C0 0]) (by positivity)
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ y : Space, (1 + ‖y‖) ^ (-(2 * α + 3 / 2)) := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := hI ▸ integral_nonneg (fun y => Real.rpow_nonneg (by positivity) _)
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ y, ‖ψ₀ y‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Kg, hKg⟩ : ∃ Kg, Kg = 6 * (max C1 0 ^ 2 * 16 ^ (2 * α - 3 / 2) + Kf ^ 2) := ⟨_, rfl⟩
  obtain ⟨Km, hKm⟩ : ∃ Km, Km = max C0 0 ^ 2 + Kf ^ 2 := ⟨_, rfl⟩
  have hα0 : 0 < α := by linarith
  have hκ : 0 < 2 * α - 3 / 2 := by linarith
  have hδ2 : 0 < (δ / 2) ^ 2 / 2 := by positivity
  have hev : ∀ᶠ T in 𝓝[>] (0 : ℝ), T < 1 ∧ 1 * (T ^ (1 / (2 * α))) ^ (1 : ℝ) < 1 / 2 ∧
      (8 * b) * (T ^ (1 / (2 * α))) ^ (1 : ℝ) < 1 ∧
      (Kg * I) * (T ^ (1 / (2 * α))) ^ (2 * α - 3 / 2) < (δ / 2) ^ 2 ∧
      (2 * |m|) * (T ^ (1 / (2 * α))) ^ (2 : ℝ) < (δ / 2) ^ 2 / 2 ∧
      (2 * (Km * I)) * (T ^ (1 / (2 * α))) ^ (2 * α - 3 / 2) < (δ / 2) ^ 2 / 2 :=
    ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds).and
      ((eventually_small hα0 one_pos (by norm_num)).and
      ((eventually_small hα0 one_pos one_pos).and
      ((eventually_small hα0 hκ (by positivity)).and
      ((eventually_small hα0 two_pos hδ2).and (eventually_small hα0 hκ hδ2)))))
  obtain ⟨T₀, hT₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨T₀, hT₀, fun T hT hTT₀ => ?_⟩
  obtain ⟨hT1, hr2, hrb, hg, hm1, hm2⟩ := hsub ⟨hT, hTT₀⟩
  rw [one_mul, Real.rpow_one] at hr2
  rw [Real.rpow_one] at hrb
  rw [Real.rpow_two] at hm1
  obtain ⟨r, hr_def⟩ : ∃ r, r = Real.sqrt (simScale α T) := ⟨_, rfl⟩
  have hrT : r = T ^ (1 / (2 * α)) := by
    rw [hr_def, simScale, Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
    congr 1
    ring
  rw [← hrT] at hr2 hrb hg hm1 hm2
  have hr : 0 < r := hrT ▸ Real.rpow_pos_of_pos hT _
  have hμ : 0 < simScale α T := Real.rpow_pos_of_pos hT _
  have hμ1 : simScale α T ≤ 1 := Real.rpow_le_one hT.le hT1.le (by positivity)
  have hμr : simScale α T = r ^ 2 := by rw [hr_def, Real.sq_sqrt hμ.le]
  have hf : ContDiff ℝ ∞ (fracApproxField α a U T 0) := by
    have h := (hA a U P hR T hT).1
    rw [contDiff_iff_contDiffAt]
    intro x
    have hm : ((0, x) : ℝ × Space) ∈ Iio T ×ˢ (univ : Set Space) := ⟨hT, trivial⟩
    have h1 := h.contDiffAt ((isOpen_Iio.prod isOpen_univ).mem_nhds hm)
    have h2 : ContDiffAt ℝ ∞ (fun y : Space => ((0, y) : ℝ × Space)) x :=
      contDiffAt_const.prodMk contDiffAt_id
    exact h1.comp x h2
  have hfd : Differentiable ℝ (fracApproxField α a U T 0) := hf.differentiable (by simp)
  have hfdiv : ∀ x, divergenceAt (fracApproxField α a U T 0) x = 0 := fun x =>
    ((hA a U P hR T hT).2.2 0 hT x).1
  have hfz : ∀ x, 1 / 8 ≤ dist x center → fracApproxField α a U T 0 x = 0 := fun x hx =>
    (((hA a U P hR T hT).2.2 0 hT x).2.1
      (by rw [show centralRadius / 2 = 1 / 8 by norm_num [centralRadius]]; exact hx)).1
  obtain ⟨h, hh⟩ : ∃ h, h = scaledAt (r ^ (2 * α - 1)) r (fracApproxField α a U T 0) := ⟨_, rfl⟩
  have hhs : ContDiff ℝ ∞ h := hh ▸ contDiff_scaledAt hf _ _
  have hhd : Differentiable ℝ h := hhs.differentiable (by simp)
  have hhdiv : ∀ y, divergenceAt h y = 0 := hh ▸ div_scaledAt hfd hfdiv _ _
  obtain ⟨R, hRd⟩ : ∃ R, R = 1 / (8 * r) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hRd]; positivity
  have hhsupp : tsupport h ⊆ Metric.closedBall 0 R := hRd ▸ hh ▸ tsupport_scaledAt hr hfz
  have hin : ∀ y, r * ‖y‖ ≤ 1 / 16 → h y = U y := fun y hy => hh ▸ inner_eq hα hA hR hT hrT y hy
  have hin' : ∀ y, r * ‖y‖ < 1 / 16 → h =ᶠ[𝓝 y] U := by
    intro y hy
    filter_upwards [(isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds hy]
      with z hz
    exact hin z hz.le
  have hout : ∀ y, 1 / 8 < r * ‖y‖ → h y = 0 := by
    intro y hy
    rw [hh, scaledAt, hfz _ (by rw [dist_scaled hr.le]; exact hy.le), smul_zero]
  have hout' : ∀ y, 1 / 8 < r * ‖y‖ → fderiv ℝ h y = 0 := by
    intro y hy
    have hz := iteratedFDeriv_eq_zero_outer hf
      (fun w hw => hfz w (by norm_num [centralRadius] at hw; linarith)) 1 (x := center + r • y)
      (by rw [dist_scaled hr.le]; norm_num [centralRadius]; linarith)
    have hz' : fderiv ℝ (fracApproxField α a U T 0) (center + r • y) = 0 := by
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_one, hz, norm_zero]
    rw [hh, fderiv_scaledAt hfd, hz', smul_zero]
  have hsh0 : ∀ y, 1 / 16 ≤ r * ‖y‖ → ‖h y‖ ≤ r ^ (2 * α - 1) * Kf := by
    intro y hy
    have hk := hKf T 0 hT hT1.le le_rfl hT (center + r • y)
      (by rw [dist_scaled hr.le]; norm_num [centralRadius]; linarith) 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at hk
    rw [hh, scaledAt, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _)]
    exact mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hr.le _)
  have hsh1 : ∀ y, 1 / 16 ≤ r * ‖y‖ → ‖fderiv ℝ h y‖ ≤ r ^ (2 * α) * Kf := by
    intro y hy
    have hk := hKf T 0 hT hT1.le le_rfl hT (center + r • y)
      (by rw [dist_scaled hr.le]; norm_num [centralRadius]; linarith) 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at hk
    have e : r ^ (2 * α - 1) * r = r ^ (2 * α) := by
      rw [← Real.rpow_add_one hr.ne']
      congr 1
      ring
    rw [hh, fderiv_scaledAt hfd, norm_smul, Real.norm_eq_abs, e,
      abs_of_pos (Real.rpow_pos_of_pos hr _)]
    exact mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hr.le _)
  have hgrad : gradEnergy (U - h) ≤ Kg * r ^ (2 * α - 3 / 2) * I := by
    unfold gradEnergy
    rw [hI]
    exact integral_weight_le hα (fun y => by positivity) (fun y => by
      have := grad_point hα hr hr2.le (hR.smooth.differentiable (by simp)) hhd hin' hout' hsh1 hU1 y
      rw [hKg]
      exact this)
  have hmass : r ^ 2 * ∫ y, ‖h y‖ ^ 2 ≤ Km * r ^ (2 * α - 3 / 2) * I := by
    rw [← integral_const_mul, hI]
    exact integral_weight_le hα (fun y => by positivity) (fun y => by
      have := mass_point hα hα2 hr hr2.le hin hout hsh0 hU0 y
      rw [hKm]
      exact this)
  have hv : extendPiece (fracApproxPiece α a U T lam 0) 0 =
      T ^ dilExponent α • toV (latticePeriodize (fracApproxField α a U T 0)) := by
    have h0 : (0 : ℝ) ≤ 1 - lam := by linarith
    rw [extendPiece, dif_pos h0, Set.IccExtend_left, (hL a U P T lam hR hT hT1.le hl hl1 0).1]
    simp [stepScale, stepStart]
  have htr : transplantField (simScale α T) h =
      (r⁻¹ * r ^ (2 * α - 1)) • latticePeriodize (fracApproxField α a U T 0) := by
    funext x
    have hper := periodize_wrap (f := fracApproxField α a U T 0)
      (fun v hv => by
        by_contra hc
        exact hv (hfz v (le_of_lt (lt_of_not_ge hc)))) x
    rw [Pi.smul_apply, hper, transplantField, simCoord, ← hr_def, hh]
    simp only [scaledAt, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have hscal : simScale α T ^ (1 / 4 : ℝ) * (r⁻¹ * r ^ (2 * α - 1)) = T ^ dilExponent α := by
    rw [hrT, simScale, ← Real.rpow_mul hT.le, ← Real.rpow_neg hT.le, ← Real.rpow_mul hT.le,
      ← Real.rpow_add hT, ← Real.rpow_add hT, dilExponent]
    congr 1
    field_simp
    ring
  have hkey : T ^ dilExponent α • toV (latticePeriodize (fracApproxField α a U T 0)) =
      simScale α T ^ (1 / 4 : ℝ) • toV (transplantField (simScale α T) h) := by
    rw [htr, Internal.TestLift.toV_smul, smul_smul, hscal]
  rw [hv, hkey, slice_zero]
  have hbR : b ≤ R := by
    rw [hRd, le_div_iff₀ (by positivity)]
    nlinarith
  have hψsupp : tsupport ψ₀ ⊆ Metric.closedBall 0 R :=
    hsupp.trans (Metric.closedBall_subset_closedBall hbR)
  obtain ⟨D, hD⟩ : ∃ D, D = ψ₀ - h := ⟨_, rfl⟩
  have hDs : ContDiff ℝ ∞ D := hD ▸ hψ.1.sub hhs
  have hDd : ∀ y, divergenceAt D y = 0 :=
    hD ▸ div_sub (hψ.1.differentiable (by simp)) hhd hψ.2.2 hhdiv
  have hDsupp : tsupport D ⊆ Metric.closedBall 0 R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Function.mem_support] at hy
    by_cases h1 : ψ₀ y = 0
    · have h2 : h y ≠ 0 := by
        intro h2
        apply hy
        rw [hD, Pi.sub_apply, h1, h2, sub_zero]
      exact hhsupp (subset_closure h2)
    · exact hψsupp (subset_closure h1)
  have hsh : IsShellScale (simScale α T) R :=
    ⟨hμ, hμ1, hRpos, le_of_eq (by rw [← hr_def, hRd]; field_simp)⟩
  obtain ⟨tD1, tD2, tD3, -⟩ := hS D _ R hDs hDd hsh hDsupp
  obtain ⟨th1, th2, th3, -⟩ := hS h _ R hhs hhdiv hsh hhsupp
  have hsplit : transplantField (simScale α T) ψ₀ =
      transplantField (simScale α T) D + transplantField (simScale α T) h := by
    funext x
    simp only [transplantField, hD, Pi.add_apply, Pi.sub_apply, smul_sub, sub_add_cancel]
  have hdiff : simScale α T ^ (1 / 4 : ℝ) • toV (transplantField (simScale α T) ψ₀) -
      simScale α T ^ (1 / 4 : ℝ) • toV (transplantField (simScale α T) h) =
      simScale α T ^ (1 / 4 : ℝ) • toV (transplantField (simScale α T) D) := by
    rw [hsplit, hV _ _ tD1 th1 tD2 th2 tD3 th3, smul_add, add_sub_cancel_right]
  rw [hdiff]
  have hψdec : IsDecayField ψ₀ := decay_of_support hψ.1 hψ.2.2 hb.le hsupp
  have hhdec : IsDecayField h := decay_of_support hhs hhdiv hRpos.le hhsupp
  have hn := hN D _ R hDs hDd hsh hDsupp
  have hge : 0 ≤ gradEnergy (ψ₀ - h) := integral_nonneg fun y => by positivity
  have hgD : (∫ y, ∑ i : Fin 3, ‖fderiv ℝ D y (unitVector i)‖ ^ 2) =
      ‖Freq.embedX ψ₀ - Freq.embedX h‖ ^ 2 := by
    rw [norm_embed_sub hE hEL hψdec hhdec, Real.sq_sqrt hge, ← hD]
    rfl
  rw [hgD] at hn
  have hgE : gradEnergy (U - h) ≤ (δ / 2) ^ 2 := by
    calc gradEnergy (U - h) ≤ Kg * r ^ (2 * α - 3 / 2) * I := hgrad
      _ = Kg * I * r ^ (2 * α - 3 / 2) := by ring
      _ ≤ (δ / 2) ^ 2 := hg.le
  have hUh : ‖Freq.embedX U - Freq.embedX h‖ ≤ δ / 2 := by
    rw [norm_embed_sub hE hEL hUdec hhdec]
    calc Real.sqrt (gradEnergy (U - h)) ≤ Real.sqrt ((δ / 2) ^ 2) := Real.sqrt_le_sqrt hgE
      _ = δ / 2 := Real.sqrt_sq (by positivity)
  have hG : ‖Freq.embedX ψ₀ - Freq.embedX h‖ ≤ ‖Freq.embedX ψ₀ - Freq.embedX U‖ + δ / 2 :=
    (norm_sub_le_norm_sub_add_norm_sub _ (Freq.embedX U) _).trans (by linarith)
  have hcs : HasCompactSupport h :=
    (isCompact_closedBall (0 : Space) R).of_isClosed_subset (isClosed_tsupport h) hhsupp
  have hi1 : Integrable ((fun v : Space => ‖v‖ ^ 2) ∘ ψ₀) :=
    ((continuous_norm.pow 2).comp hψ.1.continuous).integrable_of_hasCompactSupport
      (hψ.2.1.comp_left (by simp))
  have hi2 : Integrable ((fun v : Space => ‖v‖ ^ 2) ∘ h) :=
    ((continuous_norm.pow 2).comp hhs.continuous).integrable_of_hasCompactSupport
      (hcs.comp_left (by simp))
  replace hi1 : Integrable (fun y => ‖ψ₀ y‖ ^ 2) := hi1
  replace hi2 : Integrable (fun y => ‖h y‖ ^ 2) := hi2
  have hM : ∫ y, ‖D y‖ ^ 2 ≤ 2 * m + 2 * ∫ y, ‖h y‖ ^ 2 := by
    calc ∫ y, ‖D y‖ ^ 2 ≤ ∫ y, (2 * ‖ψ₀ y‖ ^ 2 + 2 * ‖h y‖ ^ 2) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
            ((hi1.const_mul 2).add (hi2.const_mul 2)) (Eventually.of_forall fun y => ?_)
          show ‖D y‖ ^ 2 ≤ 2 * ‖ψ₀ y‖ ^ 2 + 2 * ‖h y‖ ^ 2
          rw [hD, Pi.sub_apply]
          exact sq_norm_sub_le _ _
      _ = 2 * m + 2 * ∫ y, ‖h y‖ ^ 2 := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul, hm]
  have hTM : simScale α T * ∫ y, ‖D y‖ ^ 2 ≤ (δ / 2) ^ 2 := by
    rw [hμr]
    have h1 : r ^ 2 * ∫ y, ‖D y‖ ^ 2 ≤ r ^ 2 * (2 * m + 2 * ∫ y, ‖h y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hM (sq_nonneg r)
    have h2 : r ^ 2 * m ≤ r ^ 2 * |m| := mul_le_mul_of_nonneg_left (le_abs_self m) (sq_nonneg r)
    calc r ^ 2 * ∫ y, ‖D y‖ ^ 2 ≤ r ^ 2 * (2 * m + 2 * ∫ y, ‖h y‖ ^ 2) := h1
      _ = 2 * (r ^ 2 * m) + 2 * (r ^ 2 * ∫ y, ‖h y‖ ^ 2) := by ring
      _ ≤ 2 * (r ^ 2 * |m|) + 2 * (Km * r ^ (2 * α - 3 / 2) * I) :=
          add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
            (mul_le_mul_of_nonneg_left hmass (by norm_num))
      _ = (2 * |m|) * r ^ 2 + (2 * (Km * I)) * r ^ (2 * α - 3 / 2) := by ring
      _ ≤ (δ / 2) ^ 2 / 2 + (δ / 2) ^ 2 / 2 := add_le_add hm1.le hm2.le
      _ = (δ / 2) ^ 2 := by ring
  have hA0 := norm_nonneg (Freq.embedX ψ₀ - Freq.embedX U)
  have hG2 : ‖Freq.embedX ψ₀ - Freq.embedX h‖ ^ 2 ≤
      (‖Freq.embedX ψ₀ - Freq.embedX U‖ + δ / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hG 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  calc ‖simScale α T ^ (1 / 4 : ℝ) • toV (transplantField (simScale α T) D)‖ ^ 2
      = ‖Freq.embedX ψ₀ - Freq.embedX h‖ ^ 2 + simScale α T * ∫ y, ‖D y‖ ^ 2 := hn
    _ ≤ (‖Freq.embedX ψ₀ - Freq.embedX U‖ + δ / 2) ^ 2 + (δ / 2) ^ 2 := add_le_add hG2 hTM
    _ ≤ (‖Freq.embedX ψ₀ - Freq.embedX U‖ + δ) ^ 2 := final_arith hA0 hδ

end Breakdown.Periodic
