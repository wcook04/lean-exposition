import Breakdown.Uniqueness.StressNear
import Breakdown.Uniqueness.StressFar

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma abs_secondPartial_le_norm (θ : Space → ℝ) (i j : Fin 3) (x : Space) :
    |FundSol.secondPartial θ i j x| ≤ ‖iteratedFDeriv ℝ 2 θ x‖ := by
  unfold FundSol.secondPartial
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [unitVector, Fin.prod_univ_two]

private lemma continuous_secondPartial_smooth {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (i j : Fin 3) : Continuous (FundSol.secondPartial θ i j) := by
  unfold FundSol.secondPartial
  exact (hθ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).eval_const _

private lemma integrable_norm_sq {A : ℝ} {w : Space → Space} (hw : IsFiniteEnergyField A w) :
    Integrable (fun x => ‖w x‖ ^ 2) :=
  ⟨(hw.smooth.continuous.norm.pow 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)).2
      (hw.energy.trans_lt ENNReal.ofReal_lt_top)⟩

private lemma integrable_near_part {A : ℝ} {w : Space → Space} (hw : IsFiniteEnergyField A w)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => ∑ i, ∑ j, w x i * w x j *
      (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)) := by
  have hf := contDiff_cutoffFlux hr hw.smooth
  have hfc := hasCompactSupport_cutoffFlux hr w
  have hP := FundSol.contDiff_potential hf hfc
  obtain ⟨C, hC⟩ := FundSol.potential_decay hf hfc
  have hb : ∀ i j x, |FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x| ≤ |C| := by
    intro i j x
    have h0 : 0 ≤ (1 + ‖x‖)⁻¹ := by positivity
    have h01 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
    have h3 : (1 + ‖x‖)⁻¹ ^ (2 + 1) ≤ 1 := pow_le_one₀ h0 h01
    calc _ ≤ ‖iteratedFDeriv ℝ 2 (FundSol.potential (cutoffFlux r w)) x‖ :=
          abs_secondPartial_le_norm _ i j x
      _ ≤ C * (1 + ‖x‖)⁻¹ ^ (2 + 1) := hC 2 (by norm_num) x
      _ ≤ |C| * (1 + ‖x‖)⁻¹ ^ (2 + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      _ = |C| := mul_one _
  have hwc : Continuous w := hw.smooth.continuous
  have hρ : Continuous (radialCutoff r) := (contDiff_radialCutoff hr).continuous
  have hsec := continuous_secondPartial_smooth hP
  have hcont : Continuous (fun x => ∑ i, ∑ j, w x i * w x j *
      (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)) := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    have hi : Continuous (fun x => w x i) := (PiLp.continuous_apply 2 _ i).comp hwc
    have hj : Continuous (fun x => w x j) := (PiLp.continuous_apply 2 _ j).comp hwc
    exact (hi.mul hj).mul ((continuous_const.mul (hρ.pow 3)).mul (hsec i j))
  refine Integrable.mono' ((integrable_norm_sq hw).const_mul (9 * (4 * |C|)))
    hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have ht : ∀ i j, |w x i * w x j *
      (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)| ≤
        4 * |C| * ‖w x‖ ^ 2 := by
    intro i j
    have hi : |w x i| ≤ ‖w x‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ i
    have hj : |w x j| ≤ ‖w x‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ j
    have hρ0 := radialCutoff_nonneg r x
    have hρ1 := radialCutoff_le_one r x
    have hρ3 : radialCutoff r x ^ 3 ≤ 1 := pow_le_one₀ hρ0 hρ1
    have hc : |4 * radialCutoff r x ^ 3 *
        FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x| ≤ 4 * |C| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
        abs_of_nonneg (pow_nonneg hρ0 3)]
      have := hb i j x
      have hC0 : 0 ≤ |C| := abs_nonneg C
      nlinarith [pow_nonneg hρ0 3, abs_nonneg (FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)]
    rw [abs_mul, abs_mul]
    have hw0 : 0 ≤ ‖w x‖ := norm_nonneg _
    calc |w x i| * |w x j| * |4 * radialCutoff r x ^ 3 *
          FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x|
        ≤ ‖w x‖ * ‖w x‖ * (4 * |C|) := by
          apply mul_le_mul (mul_le_mul hi hj (abs_nonneg _) hw0) hc (abs_nonneg _)
          positivity
      _ = 4 * |C| * ‖w x‖ ^ 2 := by ring
  rw [Real.norm_eq_abs]
  calc _ ≤ ∑ i, ∑ j, |w x i * w x j *
        (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * |C| * ‖w x‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = 9 * (4 * |C|) * ‖w x‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private lemma abs_integral_add_le_of_integrable {F G : Space → ℝ} (hF : Integrable F) :
    |∫ x, (F x + G x)| ≤ |∫ x, F x| + |∫ x, G x| := by
  by_cases hG : Integrable G
  · rw [integral_add hF hG]
    exact abs_add_le _ _
  · have hFG : ¬ Integrable (fun x => F x + G x) := by
      intro h
      apply hG
      exact (h.sub hF).congr (ae_of_all _ fun x => by simp)
    rw [integral_undef hFG, abs_zero]
    positivity

theorem self_stress_le : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
    IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
      |stressPairing w w (FundSol.potential (cutoffSource r w))| ≤
        c * (cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r +
          A ^ 2 * cutoffSixthNorm r w * r ^ (-(3 / 2) : ℝ) + A ^ 3 * r ^ (-(5 / 2) : ℝ)) := by
  obtain ⟨c₁, h₁⟩ := near_stress_le
  obtain ⟨c₂, h₂⟩ := far_stress_le
  refine ⟨max (max c₁ c₂) 0, fun A w hw r hr => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hA := hw.nonneg
  have hS : 0 ≤ cutoffSixthNorm r w := by
    unfold cutoffSixthNorm
    exact Real.rpow_nonneg (integral_nonneg fun x => by
      have := radialCutoff_nonneg r x
      positivity) _
  have hX : 0 ≤ cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by
    have := Real.rpow_nonneg hS (3 / 2 : ℝ)
    have := Real.rpow_nonneg hA (3 / 2 : ℝ)
    positivity
  have hY : 0 ≤ A ^ 2 * cutoffSixthNorm r w * r ^ (-(3 / 2) : ℝ) +
      A ^ 3 * r ^ (-(5 / 2) : ℝ) := by
    have := Real.rpow_nonneg hr0.le (-(3 / 2) : ℝ)
    have := Real.rpow_nonneg hr0.le (-(5 / 2) : ℝ)
    positivity
  have hsplit : stressPairing w w (FundSol.potential (cutoffSource r w)) =
      ∫ x, ((∑ i, ∑ j, w x i * w x j *
        (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)) +
        ∑ i, ∑ j, w x i * w x j *
          (4 * ∫ y, FundSol.kernelSecondDeriv i j (x - y) *
            ((radialCutoff r y ^ 3 - radialCutoff r x ^ 3) * cutoffFlux r w y))) := by
    unfold stressPairing
    congr 1
    funext x
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [secondPartial_source_split hr0 hw.smooth hw.div_free i j x, mul_add]
  have hmax₁ : c₁ ≤ max (max c₁ c₂) 0 := (le_max_left _ _).trans (le_max_left _ _)
  have hmax₂ : c₂ ≤ max (max c₁ c₂) 0 := (le_max_right _ _).trans (le_max_left _ _)
  rw [hsplit]
  refine (abs_integral_add_le_of_integrable (integrable_near_part hw hr0)).trans ?_
  have e₁ := h₁ A w hw r hr
  have e₂ := h₂ A w hw r hr
  have e₁' : c₁ * cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r =
      c₁ * (cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by ring
  rw [e₁'] at e₁
  calc _ ≤ c₁ * (cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) +
        c₂ * (A ^ 2 * cutoffSixthNorm r w * r ^ (-(3 / 2) : ℝ) + A ^ 3 * r ^ (-(5 / 2) : ℝ)) :=
        add_le_add e₁ e₂
    _ ≤ max (max c₁ c₂) 0 * (cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) +
        max (max c₁ c₂) 0 * (A ^ 2 * cutoffSixthNorm r w * r ^ (-(3 / 2) : ℝ) +
          A ^ 3 * r ^ (-(5 / 2) : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hmax₁ hX) (mul_le_mul_of_nonneg_right hmax₂ hY)
    _ = _ := by ring

end Breakdown
