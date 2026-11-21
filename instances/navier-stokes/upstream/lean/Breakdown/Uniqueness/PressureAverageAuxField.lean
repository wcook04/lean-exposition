import Breakdown.Uniqueness.FundSolMeanValue
import Breakdown.Uniqueness.PressureMollifyAux

open scoped ContDiff ENNReal Convolution
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.Internal

private theorem field_mollifier_compact {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (FundSol.mollifier ρ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) ρ) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hx
  exact FundSol.mollifier_eq_zero hρ hx.le

private theorem field_mollify_eq (ρ : ℝ) (ϕ : Space → Space) :
    FundSol.mollify ρ ϕ = FundSol.mollifier ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ϕ := rfl

theorem contDiff_mollify_field {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ)
    {ρ : ℝ} (hρ : 0 < ρ) : ContDiff ℝ ∞ (FundSol.mollify ρ ϕ) := by
  rw [field_mollify_eq]
  exact (field_mollifier_compact hρ).contDiff_convolution_left _ (FundSol.contDiff_mollifier ρ)
    hϕ.continuous.locallyIntegrable

theorem hasCompactSupport_mollify_field {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ)
    (hc : HasCompactSupport ϕ) {ρ : ℝ} (hρ : 0 < ρ) : HasCompactSupport (FundSol.mollify ρ ϕ) := by
  rw [field_mollify_eq]
  exact (field_mollifier_compact hρ).convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hc

private theorem field_norm_convolution_le {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] E' →L[ℝ] F) {f : Space → E} {g : Space → E'} {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M)
    (hg : Integrable g) (x : Space) :
    ‖(f ⋆[L, volume] g) x‖ ≤ ‖L‖ * M * ∫ t, ‖g t‖ := by
  rw [convolution_def]
  calc ‖∫ t, L (f t) (g (x - t))‖ ≤ ∫ t, ‖L‖ * M * ‖g (x - t)‖ := by
        refine norm_integral_le_of_norm_le ((hg.norm.comp_sub_left x).const_mul _)
          (Eventually.of_forall fun t => ?_)
        exact (L.le_opNorm₂ (f t) (g (x - t))).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM t) (norm_nonneg _))
            (norm_nonneg _))
    _ = ‖L‖ * M * ∫ t, ‖g t‖ := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun t => ‖g t‖) volume x]

private theorem field_support_radius {ϕ : Space → Space} (hc : HasCompactSupport ϕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < ‖y‖ → ϕ y = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hc.isCompact.isBounded
  refine ⟨max C 0, le_max_right _ _, fun y hy => image_eq_zero_of_notMem_tsupport fun hy' => ?_⟩
  have := hC y hy'
  linarith [le_max_left C 0]

private theorem field_mollify_eq_zero {ϕ : Space → Space} {R ρ : ℝ} (hρ : 0 < ρ)
    (hR : ∀ y, R < ‖y‖ → ϕ y = 0) {x : Space} (hx : R + ρ < ‖x‖) : FundSol.mollify ρ ϕ x = 0 := by
  rw [field_mollify_eq, convolution_def]
  have h : ∀ t, (ContinuousLinearMap.lsmul ℝ ℝ) (FundSol.mollifier ρ t) (ϕ (x - t)) = 0 := by
    intro t
    rw [ContinuousLinearMap.lsmul_apply]
    by_cases ht : ‖t‖ < ρ
    · have h1 : R < ‖x - t‖ := by
        have := norm_sub_norm_le x t
        linarith
      rw [hR _ h1, smul_zero]
    · rw [FundSol.mollifier_eq_zero hρ (not_lt.1 ht), zero_smul]
  simp only [h, integral_zero]

theorem mollify_field_bounds {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ ρ, 1 ≤ ρ → ∀ x,
      (R + ρ < ‖x‖ → FundSol.mollify ρ ϕ x = 0) ∧ ‖FundSol.mollify ρ ϕ x‖ ≤ C * ρ⁻¹ ^ 3 ∧
      ‖fderiv ℝ (FundSol.mollify ρ ϕ) x‖ ≤ C * ρ⁻¹ ^ 4 ∧
      ‖iteratedFDeriv ℝ 2 (FundSol.mollify ρ ϕ) x‖ ≤ C * ρ⁻¹ ^ 5 := by
  obtain ⟨R, hR0, hR⟩ := field_support_radius hc
  obtain ⟨C0, hC0⟩ := FundSol.mollifier_le
  obtain ⟨C1, hC1⟩ := FundSol.norm_fderiv_mollifier_le
  obtain ⟨C2, hC2⟩ := FundSol.norm_iteratedFDeriv_two_mollifier_le
  set L : ℝ →L[ℝ] Space →L[ℝ] Space := ContinuousLinearMap.lsmul ℝ ℝ with hL
  set L1 := L.precompL Space with hL1
  set L2 := L1.precompL Space with hL2
  have hϕi : Integrable ϕ := hϕ.continuous.integrable_of_hasCompactSupport hc
  set I := ∫ t, ‖ϕ t‖ with hI
  set C := |‖L‖ * C0 * I| + |‖L1‖ * C1 * I| + |‖L2‖ * C2 * I| with hC
  have hk0 : ‖L‖ * C0 * I ≤ C := by
    have := le_abs_self (‖L‖ * C0 * I)
    have := abs_nonneg (‖L1‖ * C1 * I)
    have := abs_nonneg (‖L2‖ * C2 * I)
    linarith
  have hk1 : ‖L1‖ * C1 * I ≤ C := by
    have := le_abs_self (‖L1‖ * C1 * I)
    have := abs_nonneg (‖L‖ * C0 * I)
    have := abs_nonneg (‖L2‖ * C2 * I)
    linarith
  have hk2 : ‖L2‖ * C2 * I ≤ C := by
    have := le_abs_self (‖L2‖ * C2 * I)
    have := abs_nonneg (‖L‖ * C0 * I)
    have := abs_nonneg (‖L1‖ * C1 * I)
    linarith
  refine ⟨R, C, hR0, by positivity, fun ρ hρ x => ⟨fun hx => field_mollify_eq_zero
    (lt_of_lt_of_le one_pos hρ) hR hx, ?_, ?_, ?_⟩⟩
  all_goals have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  all_goals have hψc := field_mollifier_compact hρ0
  all_goals have hψs := FundSol.contDiff_mollifier ρ
  · rw [field_mollify_eq]
    have h := field_norm_convolution_le L (M := C0 * ρ⁻¹ ^ 3) (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (FundSol.mollifier_nonneg hρ0 t)]; exact hC0 ρ hρ0 t) hϕi x
    refine h.trans ?_
    have e : ‖L‖ * (C0 * ρ⁻¹ ^ 3) * I = (‖L‖ * C0 * I) * ρ⁻¹ ^ 3 := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact hk0
  · have hd : ∀ y, HasFDerivAt (FundSol.mollify ρ ϕ)
        ((fderiv ℝ (FundSol.mollifier ρ) ⋆[L1, volume] ϕ) y) y := fun y => by
      rw [field_mollify_eq]
      exact hψc.hasFDerivAt_convolution_left L (hψs.of_le (by exact_mod_cast le_top))
        hϕ.continuous.locallyIntegrable y
    rw [(hd x).fderiv]
    have h := field_norm_convolution_le L1 (M := C1 * ρ⁻¹ ^ 4) (fun t => hC1 ρ hρ0 t) hϕi x
    refine h.trans ?_
    have e : ‖L1‖ * (C1 * ρ⁻¹ ^ 4) * I = (‖L1‖ * C1 * I) * ρ⁻¹ ^ 4 := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact hk1
  · have hd : ∀ y, HasFDerivAt (FundSol.mollify ρ ϕ)
        ((fderiv ℝ (FundSol.mollifier ρ) ⋆[L1, volume] ϕ) y) y := fun y => by
      rw [field_mollify_eq]
      exact hψc.hasFDerivAt_convolution_left L (hψs.of_le (by exact_mod_cast le_top))
        hϕ.continuous.locallyIntegrable y
    have hfd : fderiv ℝ (FundSol.mollify ρ ϕ) = fderiv ℝ (FundSol.mollifier ρ) ⋆[L1, volume] ϕ :=
      funext fun y => (hd y).fderiv
    have hψ1s : ContDiff ℝ ∞ (fderiv ℝ (FundSol.mollifier ρ)) :=
      (contDiff_infty_iff_fderiv.1 hψs).2
    have hψ1c : HasCompactSupport (fderiv ℝ (FundSol.mollifier ρ)) := hψc.fderiv (𝕜 := ℝ)
    have hd2 := hψ1c.hasFDerivAt_convolution_left L1 (hψ1s.of_le (by exact_mod_cast le_top))
      (hϕ.continuous.locallyIntegrable (μ := volume)) x
    have hn : ‖iteratedFDeriv ℝ 2 (FundSol.mollify ρ ϕ) x‖ =
        ‖fderiv ℝ (fderiv ℝ (FundSol.mollify ρ ϕ)) x‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [hn, hfd, hd2.fderiv]
    have hb : ∀ t, ‖fderiv ℝ (fderiv ℝ (FundSol.mollifier ρ)) t‖ ≤ C2 * ρ⁻¹ ^ 5 := fun t => by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact hC2 ρ hρ0 t
    have h := field_norm_convolution_le L2 (M := C2 * ρ⁻¹ ^ 5) hb hϕi x
    refine h.trans ?_
    have e : ‖L2‖ * (C2 * ρ⁻¹ ^ 5) * I = (‖L2‖ * C2 * I) * ρ⁻¹ ^ 5 := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact hk2

end Breakdown.Internal
