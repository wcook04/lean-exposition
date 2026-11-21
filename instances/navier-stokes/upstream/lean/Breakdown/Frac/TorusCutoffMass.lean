import Breakdown.Frac.TorusApproxCloseAux
import Breakdown.Frac.TorusResidualOuterBound

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CutoffMass.Internal

open FracOuterBoundInternal ApproxSizes.Internal Cutoff.Internal

theorem field_bound (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hD : FracSelfSimilarDecay α)
    (a : ℝ) (U : Space → Space) (P : Space → ℝ) (hU : IsRotatingProfile α a 1 U P) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      ‖fracApproxField α a U T t x‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1)) + B := by
  obtain ⟨C, hC⟩ := hD a U P hU
  obtain ⟨KA, hKA0, hKA⟩ := potential_bound α h1 h2 hD a U P hU
  obtain ⟨G, hG0, hG⟩ := centralCut_bounds
  refine ⟨max C 0, ‖crossBilinear‖ * G * KA, le_max_right _ _, by positivity, ?_⟩
  intro T t hT hT1 ht0 htT x
  have hform : fracApproxField α a U T t x = centralCut x • fracSelfSimilar α a U T t x +
      crossBilinear (gradientAt centralCut x) (homotopyPotential center (fracSelfSimilar α a U T t) x) :=
    rfl
  rw [hform]
  have hμ : 0 < T - t := by linarith
  have hX : 0 ≤ ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1)) :=
    Real.rpow_nonneg (by positivity) _
  have hg : ‖fracSelfSimilar α a U T t x‖ ≤
      max C 0 * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1)) := by
    have hb := (hC T t hT hT1 ht0 htT x).1 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
  have hp1 : ‖centralCut x • fracSelfSimilar α a U T t x‖ ≤
      max C 0 * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1)) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |centralCut x| * ‖fracSelfSimilar α a U T t x‖ ≤ 1 * ‖fracSelfSimilar α a U T t x‖ :=
          mul_le_mul_of_nonneg_right (hG x).1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hg
  have hp2 : ‖crossBilinear (gradientAt centralCut x)
      (homotopyPotential center (fracSelfSimilar α a U T t) x)‖ ≤ ‖crossBilinear‖ * G * KA := by
    by_cases hsh : 1 / 16 ≤ dist x center ∧ dist x center ≤ 1 / 8
    · have hp : ‖homotopyPotential center (fracSelfSimilar α a U T t) x‖ ≤ KA := by
        have := hKA T t hT hT1 ht0 htT x hsh.1 hsh.2 0 (by norm_num)
        rwa [norm_iteratedFDeriv_zero] at this
      refine (crossBilinear.le_opNorm₂ _ _).trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hG x).2 (norm_nonneg _)) hp (norm_nonneg _)
        (by positivity)
    · have hz : gradientAt centralCut x = 0 := by
        rcases not_and_or.1 hsh with h | h
        · exact ApproxField.Internal.gradient_eq_zero_of_fderiv
            (ApproxField.Internal.fderiv_centralCut_inner (by norm_num [centralRadius]; linarith))
        · exact ApproxField.Internal.gradient_eq_zero_of_fderiv
            (ApproxField.Internal.fderiv_centralCut_outer (by norm_num [centralRadius]; linarith))
      rw [hz, map_zero, zero_apply, norm_zero]
      positivity
  exact (norm_add_le _ _).trans (add_le_add hp1 hp2)

theorem scale_cancel {α μ r : ℝ} (hα : 0 < α) (hμ : 0 < μ) (hr : 0 ≤ r) :
    μ ^ (1 - 1 / (2 * α)) * (μ ^ (1 / (2 * α)) * (1 + r)) ^ (-(2 * α - 1)) =
      (1 + r) ^ (-(2 * α - 1)) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hμ.le _) (by linarith), ← Real.rpow_mul hμ.le, ← mul_assoc,
    ← Real.rpow_add hμ]
  have he : 1 - 1 / (2 * α) + 1 / (2 * α) * -(2 * α - 1) = 0 := by field_simp; ring
  rw [he, Real.rpow_zero, one_mul]

theorem scale_one {α μ : ℝ} (hμ : 0 < μ) : μ ^ (1 / (2 * α)) * μ ^ (-(1 / (2 * α))) = 1 := by
  rw [← Real.rpow_add hμ, add_neg_cancel, Real.rpow_zero]


theorem cut_sq_le (α : ℝ) (h1 : 1 < α) (hA : FracApproxFieldProperties α) {a : ℝ} {U : Space → Space}
    {P : Space → ℝ} (hU : IsRotatingProfile α a 1 U P) {C B T t : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hT : 0 < T) (htT : t < T)
    (hF : ∀ x : Space, ‖fracApproxField α a U T t x‖ ≤
        C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1)) + B) (y : Space) :
    ‖fracCutAt α a U T t (T - t) y‖ ^ 2 ≤ (Iic ((1 / 8) * (T - t) ^ (-(1 / (2 * α))))).indicator
      (fun r : ℝ => 2 * (C * (1 + r) ^ (-(2 * α - 1))) ^ 2 + 2 * ((T - t) ^ (1 - 1 / (2 * α)) * B) ^ 2)
      ‖y‖ := by
  have hμ : 0 < T - t := by linarith
  have hα : 0 < α := by linarith
  have hs : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  have hd : ‖center + (T - t) ^ (1 / (2 * α)) • y - center‖ = (T - t) ^ (1 / (2 * α)) * ‖y‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  by_cases hy : ‖y‖ ≤ (1 / 8) * (T - t) ^ (-(1 / (2 * α)))
  · rw [indicator_of_mem (show ‖y‖ ∈ Iic _ from hy)]
    have hb := hF (center + (T - t) ^ (1 / (2 * α)) • y)
    rw [hd] at hb
    have hm : (T - t) ^ (1 / (2 * α)) + (T - t) ^ (1 / (2 * α)) * ‖y‖ =
        (T - t) ^ (1 / (2 * α)) * (1 + ‖y‖) := by ring
    rw [hm] at hb
    have hw : 0 < (T - t) ^ (1 - 1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
    have hn : ‖fracCutAt α a U T t (T - t) y‖ ≤
        C * (1 + ‖y‖) ^ (-(2 * α - 1)) + (T - t) ^ (1 - 1 / (2 * α)) * B := by
      unfold fracCutAt
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hw]
      calc (T - t) ^ (1 - 1 / (2 * α)) * ‖fracApproxField α a U T t (center + (T - t) ^ (1 / (2 * α)) • y)‖
          ≤ (T - t) ^ (1 - 1 / (2 * α)) *
              (C * ((T - t) ^ (1 / (2 * α)) * (1 + ‖y‖)) ^ (-(2 * α - 1)) + B) :=
            mul_le_mul_of_nonneg_left hb hw.le
        _ = C * ((T - t) ^ (1 - 1 / (2 * α)) * ((T - t) ^ (1 / (2 * α)) * (1 + ‖y‖)) ^ (-(2 * α - 1)))
              + (T - t) ^ (1 - 1 / (2 * α)) * B := by ring
        _ = _ := by rw [scale_cancel hα hμ (norm_nonneg y)]
    have h0 : 0 ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1)) :=
      mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
    have h0' : 0 ≤ (T - t) ^ (1 - 1 / (2 * α)) * B := mul_nonneg hw.le hB
    calc _ ≤ (C * (1 + ‖y‖) ^ (-(2 * α - 1)) + (T - t) ^ (1 - 1 / (2 * α)) * B) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ _ := by
          nlinarith [sq_nonneg (C * (1 + ‖y‖) ^ (-(2 * α - 1)) - (T - t) ^ (1 - 1 / (2 * α)) * B)]
  · rw [indicator_of_notMem (show ‖y‖ ∉ Iic _ from hy)]
    have hfar : centralRadius / 2 ≤ dist (center + (T - t) ^ (1 / (2 * α)) • y) center := by
      rw [dist_eq_norm, hd]
      have h8 := mul_lt_mul_of_pos_left (lt_of_not_ge hy) hs
      rw [show (T - t) ^ (1 / (2 * α)) * ((1 / 8) * (T - t) ^ (-(1 / (2 * α)))) =
        (1 / 8) * ((T - t) ^ (1 / (2 * α)) * (T - t) ^ (-(1 / (2 * α)))) by ring, scale_one hμ] at h8
      rw [show centralRadius / 2 = 1 / 8 by norm_num [centralRadius]]
      linarith
    have hz := (((hA a U P hU T hT).2.2 t htT _).2.1 hfar).1
    unfold fracCutAt
    rw [hz, smul_zero, norm_zero]
    norm_num

theorem sq_rpow_le {A p r : ℝ} (hr : 0 < r) (hp : 0 ≤ p) :
    r ^ 2 * (A * (1 + r) ^ (-p)) ^ 2 ≤ A ^ 2 * r ^ (2 - 2 * p) := by
  have hle : (1 + r) ^ (-p) ≤ r ^ (-p) := Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
  have h0 : 0 ≤ (1 + r) ^ (-p) := Real.rpow_nonneg (by linarith) _
  have hsq : ((1 + r) ^ (-p)) ^ 2 ≤ (r ^ (-p)) ^ 2 := pow_le_pow_left₀ h0 hle 2
  have hid : r ^ 2 * (r ^ (-p)) ^ 2 = r ^ (2 - 2 * p) := by
    rw [← Real.rpow_natCast (r ^ (-p)) 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r 2,
      ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  calc r ^ 2 * (A * (1 + r) ^ (-p)) ^ 2 = A ^ 2 * (r ^ 2 * ((1 + r) ^ (-p)) ^ 2) := by ring
    _ ≤ A ^ 2 * (r ^ 2 * (r ^ (-p)) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) (sq_nonneg A)
    _ = _ := by rw [hid]

theorem radial_le {ρ A b p : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b) (hp0 : 0 ≤ p) (hp : p < 3 / 2) :
    Integrable (fun y : Space =>
      (Iic ρ).indicator (fun r : ℝ => 2 * (A * (1 + r) ^ (-p)) ^ 2 + b) ‖y‖) ∧
    ∫ y : Space, (Iic ρ).indicator (fun r : ℝ => 2 * (A * (1 + r) ^ (-p)) ^ 2 + b) ‖y‖ ≤
      3 * volume.real (Metric.ball (0 : Space) 1) *
        (2 * A ^ 2 * (ρ ^ (3 - 2 * p) / (3 - 2 * p)) + b * ρ ^ 2 * ρ) := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = (Iic ρ).indicator
      (fun r : ℝ => 2 * (A * (1 + r) ^ (-p)) ^ 2 + b) := ⟨_, rfl⟩
  rw [← hg]
  have hgm : Measurable g := hg ▸ (Measurable.indicator (by fun_prop) measurableSet_Iic)
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun r => 2 * A ^ 2 * r ^ (2 - 2 * p) + b * ρ ^ 2 := ⟨_, rfl⟩
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖r ^ 2 * g r‖ ≤ (Ioc 0 ρ).indicator f r := by
    intro r hr
    have hr0 : 0 < r := hr
    by_cases hrρ : r ≤ ρ
    · rw [hg, indicator_of_mem (show r ∈ Iic ρ from hrρ),
        indicator_of_mem (show r ∈ Ioc 0 ρ from ⟨hr0, hrρ⟩), hf]
      have h2 := sq_rpow_le (A := A) hr0 hp0
      have h3 : r ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr0.le hrρ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h3 hb]
    · rw [hg, indicator_of_notMem (show r ∉ Iic ρ from hrρ),
        indicator_of_notMem (show r ∉ Ioc 0 ρ from fun h => hrρ h.2)]
      simp
  have hex : -1 < 2 - 2 * p := by linarith
  have hII : IntervalIntegrable f volume 0 ρ := by
    rw [hf]
    exact ((intervalIntegral.intervalIntegrable_rpow' hex).const_mul _).add intervalIntegrable_const
  have hion : IntegrableOn f (Ioc 0 ρ) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ).1 hII
  have hind : Integrable ((Ioc 0 ρ).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioc).2 hion
  have hI : IntegrableOn (fun r => r ^ 2 * g r) (Ioi 0) :=
    hind.integrableOn.mono' (((measurable_id.pow_const 2).mul hgm).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))
  have hform := integral_fun_norm_addHaar (volume : Measure Space) g
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul] at hform
  refine ⟨?_, ?_⟩
  · rw [integrable_fun_norm_addHaar (volume : Measure Space)]
    simpa [finrank_euclideanSpace_fin] using hI
  · rw [hform]
    have hV : 0 ≤ volume.real (Metric.ball (0 : Space) 1) := measureReal_nonneg
    have hval : ∫ r in Ioc 0 ρ, f r = 2 * A ^ 2 * (ρ ^ (3 - 2 * p) / (3 - 2 * p)) + b * ρ ^ 2 * ρ := by
      rw [← intervalIntegral.integral_of_le hρ, hf, intervalIntegral.integral_add
        ((intervalIntegral.intervalIntegrable_rpow' hex).const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, integral_rpow (Or.inl hex), intervalIntegral.integral_const]
      have h3 : (2 - 2 * p + 1) = 3 - 2 * p := by ring
      rw [h3, Real.zero_rpow (by linarith)]
      simp
      ring
    have hle : ∫ r in Ioi (0 : ℝ), r ^ (3 - 1) * g r ≤
        2 * A ^ 2 * (ρ ^ (3 - 2 * p) / (3 - 2 * p)) + b * ρ ^ 2 * ρ := by
      calc ∫ r in Ioi (0 : ℝ), r ^ (3 - 1) * g r
          ≤ ∫ r in Ioi (0 : ℝ), (Ioc 0 ρ).indicator f r :=
            setIntegral_mono_on hI hind.integrableOn measurableSet_Ioi
              (fun r hr => (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hbound r hr))
        _ = ∫ r, (Ioc 0 ρ).indicator f r :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr =>
              indicator_of_notMem (fun h => hr h.1) _
        _ = ∫ r in Ioc 0 ρ, f r := integral_indicator measurableSet_Ioc
        _ = _ := hval
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hle hV]

theorem power_identity {α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    (μ ^ (1 - 1 / (2 * α))) ^ 2 * (μ ^ (-(1 / (2 * α)))) ^ 3 = μ ^ (-((5 - 4 * α) / (2 * α))) := by
  rw [← Real.rpow_natCast (μ ^ (1 - 1 / (2 * α))) 2, ← Real.rpow_natCast (μ ^ (-(1 / (2 * α)))) 3,
    ← Real.rpow_mul hμ.le, ← Real.rpow_mul hμ.le, ← Real.rpow_add hμ]
  congr 1
  push_cast
  field_simp
  ring

theorem radius_identity {α μ : ℝ} (hμ : 0 < μ) :
    ((1 / 8) * μ ^ (-(1 / (2 * α)))) ^ (3 - 2 * (2 * α - 1)) =
      (1 / 8 : ℝ) ^ (5 - 4 * α) * μ ^ (-((5 - 4 * α) / (2 * α))) := by
  rw [show (3 - 2 * (2 * α - 1)) = 5 - 4 * α by ring,
    Real.mul_rpow (by norm_num) (Real.rpow_nonneg hμ.le _), ← Real.rpow_mul hμ.le]
  congr 2
  ring

end CutoffMass.Internal

open CutoffMass.Internal

theorem fracCutoffMass (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (hA : FracApproxFieldProperties α)
    (hSD : FracSelfSimilarDecay α) :
    ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P → ∃ K : ℝ,
      ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T →
        ∫ y, ‖fracCutAt α a U T t (T - t) y‖ ^ 2 ≤ K * (T - t) ^ (-((5 - 4 * α) / (2 * α))) := by
  intro a U P hU
  obtain ⟨C, B, hC, hB, hF⟩ := field_bound α hα hα2 hSD a U P hU
  refine ⟨3 * volume.real (Metric.ball (0 : Space) 1) *
    (2 * C ^ 2 * ((1 / 8 : ℝ) ^ (5 - 4 * α) / (5 - 4 * α)) + 2 * B ^ 2 / 512), ?_⟩
  intro T t hT hT1 ht0 htT
  have hμ : 0 < T - t := by linarith
  have hα0 : 0 < α := by linarith
  have hρ : 0 ≤ (1 / 8) * (T - t) ^ (-(1 / (2 * α))) := by positivity
  obtain ⟨hint, hle⟩ := radial_le (ρ := (1 / 8) * (T - t) ^ (-(1 / (2 * α)))) (A := C)
    (b := 2 * ((T - t) ^ (1 - 1 / (2 * α)) * B) ^ 2) (p := 2 * α - 1) hρ (by positivity)
    (by linarith) (by linarith)
  have h1 := radius_identity (α := α) hμ
  have h2 := power_identity hα0 hμ
  have h3 : 3 - 2 * (2 * α - 1) = 5 - 4 * α := by ring
  calc ∫ y, ‖fracCutAt α a U T t (T - t) y‖ ^ 2
      ≤ ∫ y : Space, (Iic ((1 / 8) * (T - t) ^ (-(1 / (2 * α))))).indicator
          (fun r : ℝ => 2 * (C * (1 + r) ^ (-(2 * α - 1))) ^ 2 +
            2 * ((T - t) ^ (1 - 1 / (2 * α)) * B) ^ 2) ‖y‖ :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) hint
          (Eventually.of_forall fun y => cut_sq_le α hα hA hU hC hB hT htT
            (hF T t hT hT1 ht0 htT) y)
    _ ≤ _ := hle
    _ = _ := by
        rw [h1, h3]
        have h4 : 2 * ((T - t) ^ (1 - 1 / (2 * α)) * B) ^ 2 *
            ((1 / 8) * (T - t) ^ (-(1 / (2 * α)))) ^ 2 * ((1 / 8) * (T - t) ^ (-(1 / (2 * α)))) =
            2 * B ^ 2 / 512 * ((T - t) ^ (1 - 1 / (2 * α))) ^ 2 * ((T - t) ^ (-(1 / (2 * α)))) ^ 3 := by
          ring
        rw [h4, mul_assoc (2 * B ^ 2 / 512), h2]
        ring

end Breakdown.Periodic
