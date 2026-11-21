import Breakdown.Frac.StTorusStepApprox
import Breakdown.Torus.ApproxSizes
import Breakdown.Frac.TorusResidualOuterBound

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def fracCut (α a : ℝ) (U : Space → Space) (T t : ℝ) (y : Space) : Space :=
  (T - t) ^ (1 - 1 / (2 * α)) • fracApproxField α a U T t (center + (T - t) ^ (1 / (2 * α)) • y)

def FracShellGradientBound (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∃ G : ℝ,
    ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center →
      ‖fderiv ℝ (fracApproxField α a U T t) x‖ ≤ G

open FracOuterBoundInternal Cutoff.Internal in
theorem fracShellGradientBound (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (hA : FracApproxFieldProperties α)
    (hSD : FracSelfSimilarDecay α) : FracShellGradientBound α := by
  intro a U P hU
  obtain ⟨C, hC⟩ := hSD a U P hU
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; exact le_max_right _ _
  have hCC : C ≤ C' := by rw [hC']; exact le_max_left _ _
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (1 / 16 : ℝ) ^ (-(5 : ℝ)) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact Real.rpow_nonneg (by norm_num) _
  obtain ⟨KA, hKA0, hKA⟩ := potential_bound α hα hα2 hSD a U P hU
  obtain ⟨Kc, hKc0, hKc⟩ := bounded_upto3 ApproxField.Internal.contDiff_centralCut
    (centralBump.hasCompactSupport : HasCompactSupport centralCut)
  obtain ⟨Kd, hKd0, hKd⟩ := bounded_upto3 ApproxField.Internal.contDiff_gradient_centralCut
    gradient_support
  have hB0 : 0 ≤ ‖crossBilinear‖ := norm_nonneg _
  refine ⟨8 * (Kc * (C' * N)) + ‖crossBilinear‖ * (8 * (Kd * KA)), fun T t hT hT1 ht0 htT y hy => ?_⟩
  have hμ : 0 < T - t := by linarith
  have hg : ContDiff ℝ ∞ (fracSelfSimilar α a U T t) := selfSimilar_contDiff hU.smooth T t
  have hP : ContDiff ℝ ∞ (homotopyPotential center (fracSelfSimilar α a U T t)) := by
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
    (crossBilinear.contDiff.comp ApproxField.Internal.contDiff_gradient_centralCut).clm_apply hP
  rw [← norm_iteratedFDeriv_one]
  have hy1 : 1 / 16 ≤ dist y center := by norm_num [centralRadius] at hy; linarith
  rcases le_total (dist y center) (1 / 8) with hle | hge
  · rw [hform]
    show ‖iteratedFDeriv ℝ 1 ((fun w => centralCut w • fracSelfSimilar α a U T t w) +
      (fun w => crossBilinear (gradientAt centralCut w)
        (homotopyPotential center (fracSelfSimilar α a U T t) w))) y‖ ≤ _
    rw [iteratedFDeriv_add_apply (hs1.contDiffAt.of_le (nat_le_infty 1))
      (hs2.contDiffAt.of_le (nat_le_infty 1))]
    have hsm := norm_iteratedFDeriv_smul_le ApproxField.Internal.contDiff_centralCut hg y
      (nat_le_infty 1)
    have hsum1 := binom_sum_le3 (a := fun i => ‖iteratedFDeriv ℝ i centralCut y‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) y‖)
      (fun i hi => ⟨norm_nonneg _, hKc i hi y⟩) (fun i hi => ⟨norm_nonneg _, hgb y hy1 i hi⟩)
      (by norm_num : 1 ≤ 3)
    have hbl := crossBilinear.norm_iteratedFDeriv_le_of_bilinear
      ApproxField.Internal.contDiff_gradient_centralCut hP y (nat_le_infty 1)
    have hsum2 := binom_sum_le3 (a := fun i => ‖iteratedFDeriv ℝ i (gradientAt centralCut) y‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (homotopyPotential center (fracSelfSimilar α a U T t)) y‖)
      (fun i hi => ⟨norm_nonneg _, hKd i hi y⟩)
      (fun i hi => ⟨norm_nonneg _, hKA T t hT hT1 ht0 htT y hy1 hle i hi⟩) (by norm_num : 1 ≤ 3)
    have hb2 := mul_le_mul_of_nonneg_left hsum2 hB0
    refine (norm_add_le _ _).trans ?_
    linarith
  · rcases eq_or_lt_of_le hge with heq | hlt
    · have hge' : centralRadius / 2 ≤ dist y center := by rw [← heq]; norm_num [centralRadius]
      rw [iteratedFDeriv_eq_zero_outer (hform ▸ (hs1.add hs2))
        (fun w hw => ((hA a U P hU T hT).2.2 t htT w).2.1 hw |>.1) 1 hge', norm_zero]
      positivity
    · rw [iteratedFDeriv_eq_zero_outer (hform ▸ (hs1.add hs2))
        (fun w hw => ((hA a U P hU T hT).2.2 t htT w).2.1 hw |>.1) 1 (by norm_num [centralRadius]; linarith),
        norm_zero]
      positivity

end Breakdown.Periodic
