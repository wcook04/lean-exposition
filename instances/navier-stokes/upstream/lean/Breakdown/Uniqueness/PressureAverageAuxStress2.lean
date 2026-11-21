import Breakdown.Uniqueness.FundSolPointwiseAux2
import Breakdown.Uniqueness.PressureMollifyAux

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.Internal

theorem norm_iteratedFDeriv_convolution_field_le {ϕ : Space → Space} (hϕ : Continuous ϕ)
    (hϕc : HasCompactSupport ϕ) (k : ℕ) :
    ∀ {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
      [NormedSpace ℝ G] (L : E →L[ℝ] Space →L[ℝ] G) (f : Space → E), ContDiff ℝ ∞ f →
      HasCompactSupport f → ∀ M : ℝ, (∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M) → ∀ x,
      ‖iteratedFDeriv ℝ k (convolution f ϕ L volume) x‖ ≤ ‖L‖ * M * ∫ y, ‖ϕ y‖ := by
  induction k with
  | zero =>
    intro E G _ _ _ _ L f hf hfc M hM x
    rw [norm_iteratedFDeriv_zero, convolution_def]
    have hM' : ∀ y, ‖f y‖ ≤ M := fun y => by simpa using hM y
    have hint : Integrable (fun t => ‖L‖ * M * ‖ϕ (x - t)‖) :=
      ((hϕ.integrable_of_hasCompactSupport hϕc).norm.comp_sub_left x).const_mul _
    calc ‖∫ t, L (f t) (ϕ (x - t))‖ ≤ ∫ t, ‖L‖ * M * ‖ϕ (x - t)‖ :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => by
            refine (L.le_opNorm₂ _ _).trans ?_
            have := hM' t
            gcongr)
      _ = ‖L‖ * M * ∫ y, ‖ϕ y‖ := by
          rw [integral_const_mul, integral_sub_left_eq_self (fun y => ‖ϕ y‖)]
  | succ k ih =>
    intro E G _ _ _ _ L f hf hfc M hM x
    have hd : fderiv ℝ (convolution f ϕ L volume) =
        convolution (fderiv ℝ f) ϕ (L.precompL Space) volume := by
      funext y
      exact (hfc.hasFDerivAt_convolution_left L (hf.of_le (by exact_mod_cast le_top))
        hϕ.locallyIntegrable y).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hd]
    have h1 := ih (L.precompL Space) (fderiv ℝ f) (hf.fderiv_right (m := ∞) le_rfl)
      (hfc.fderiv (𝕜 := ℝ)) M (fun y => by rw [norm_iteratedFDeriv_fderiv]; exact hM y) x
    refine h1.trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hI0 : 0 ≤ ∫ y, ‖ϕ y‖ := integral_nonneg fun y => norm_nonneg _
    have hL := ContinuousLinearMap.norm_precompL_le (Eₗ := Space) L
    gcongr

private theorem contDiff_bump_aux : ContDiff ℝ ∞ FundSol.bumpProfile := by
  unfold FundSol.bumpProfile
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ (E := Space))))

private theorem bump_eq_zero_aux {x : Space} (hx : 1 < ‖x‖) : FundSol.bumpProfile x = 0 := by
  unfold FundSol.bumpProfile
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith

private theorem hasCompactSupport_bump_aux : HasCompactSupport FundSol.bumpProfile :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1) fun x hx => by
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact bump_eq_zero_aux hx

private theorem mollifier_eq_aux (ρ : ℝ) : FundSol.mollifier ρ =
    (ρ ^ 3 * ∫ y, FundSol.bumpProfile y)⁻¹ •
      (FundSol.bumpProfile ∘ (ρ⁻¹ • ContinuousLinearMap.id ℝ Space)) := by
  funext x
  simp [FundSol.mollifier, smul_eq_mul]

theorem contDiff_mollifier_aux (ρ : ℝ) : ContDiff ℝ ∞ (FundSol.mollifier ρ) := by
  rw [mollifier_eq_aux]
  exact (contDiff_bump_aux.comp (ContinuousLinearMap.contDiff (ρ⁻¹ • ContinuousLinearMap.id ℝ Space))).const_smul
    ((ρ ^ 3 * ∫ y, FundSol.bumpProfile y)⁻¹ : ℝ)

theorem hasCompactSupport_mollifier_aux {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (FundSol.mollifier ρ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) ρ) fun x hx => by
    rw [mem_closedBall_zero_iff, not_le] at hx
    simp only [FundSol.mollifier]
    rw [bump_eq_zero_aux, mul_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, inv_mul_eq_div, one_lt_div hρ]
    exact hx

theorem norm_iteratedFDeriv_mollifier_aux (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ, 0 < ρ → ∀ x,
    ‖iteratedFDeriv ℝ k (FundSol.mollifier ρ) x‖ ≤ C * ρ⁻¹ ^ (k + 3) := by
  obtain ⟨B, hB⟩ := (contDiff_bump_aux.continuous_iteratedFDeriv (m := k)
    (by exact_mod_cast le_top)).bounded_above_of_compact_support
    (hasCompactSupport_bump_aux.iteratedFDeriv (𝕜 := ℝ) k)
  set I := ∫ y, FundSol.bumpProfile y
  refine ⟨|I|⁻¹ * max B 0, by positivity, fun ρ hρ x => ?_⟩
  set Lρ : Space →L[ℝ] Space := ρ⁻¹ • ContinuousLinearMap.id ℝ Space
  have hLn : ‖Lρ‖ ≤ ρ⁻¹ := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hρ)]
    exact mul_le_of_le_one_right (inv_pos.2 hρ).le ContinuousLinearMap.norm_id_le
  rw [mollifier_eq_aux, iteratedFDeriv_const_smul_apply
    ((contDiff_bump_aux.comp (ContinuousLinearMap.contDiff (ρ⁻¹ • ContinuousLinearMap.id ℝ Space))).contDiffAt.of_le
      (by exact_mod_cast le_top)), norm_smul,
    Lρ.iteratedFDeriv_comp_right contDiff_bump_aux x (by exact_mod_cast le_top)]
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k FundSol.bumpProfile (Lρ x)) (fun _ => Lρ)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ‖iteratedFDeriv ℝ k FundSol.bumpProfile (Lρ x)‖ * ‖Lρ‖ ^ k ≤ max B 0 * ρ⁻¹ ^ k := by
    gcongr
    · exact le_max_of_le_left (hB _)
  have h3 : ‖(ρ ^ 3 * I)⁻¹‖ = |I|⁻¹ * ρ⁻¹ ^ 3 := by
    rw [Real.norm_eq_abs, abs_inv, abs_mul, abs_of_pos (pow_pos hρ 3), mul_inv, inv_pow]; ring
  rw [h3]
  calc |I|⁻¹ * ρ⁻¹ ^ 3 * ‖(iteratedFDeriv ℝ k FundSol.bumpProfile (Lρ x)).compContinuousLinearMap
        fun _ => Lρ‖ ≤ |I|⁻¹ * ρ⁻¹ ^ 3 * (max B 0 * ρ⁻¹ ^ k) := by
        gcongr; exact h1.trans h2
    _ = |I|⁻¹ * max B 0 * ρ⁻¹ ^ (k + 3) := by ring

theorem abs_potential_le_of_support : ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : Space → ℝ) (A r : ℝ), 0 < r →
    (∀ t, |g t| ≤ A) → (∀ t, r < ‖t‖ → g t = 0) → ∀ z, |FundSol.potential g z| ≤ A * K * r ^ 2 := by
  set V := volume.real (ball (0 : Space) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨(4 * π)⁻¹ * 54 * V, by positivity, fun g A r hr hA hs z => ?_⟩
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  rcases le_or_gt ‖z‖ (2 * r) with hz | hz
  · have h := FundSol.Internal.abs_potential_le (g := g) (A := A) (by linarith : (0 : ℝ) < 2 * r) hA
      (fun t ht => hs t (by linarith)) hz
    rw [FundSol.Internal.integral_ballPow_one (by linarith)] at h
    refine h.trans (le_of_eq ?_)
    ring
  · rw [FundSol.Internal.potential_apply, ← Real.norm_eq_abs]
    have hint : Integrable (fun t => A * (4 * π)⁻¹ * r⁻¹ * FundSol.Internal.ballPow 0 (2 * r) t) :=
      (FundSol.Internal.integrable_ballPow (n := 0) (by norm_num) _).const_mul _
    refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [Real.norm_eq_abs, abs_mul, FundSol.Internal.abs_kernel]
      by_cases ht : r < ‖t‖
      · rw [hs t ht, abs_zero, zero_mul]
        exact mul_nonneg (by positivity) (FundSol.Internal.ballPow_nonneg _ _ _)
      · have ht' : ‖t‖ ≤ r := not_lt.1 ht
        rw [FundSol.Internal.ballPow_of_lt (by linarith), pow_zero, mul_one]
        have hzt : r ≤ ‖z - t‖ := by
          have := norm_sub_norm_le z t
          linarith
        have hinv : ‖z - t‖⁻¹ ≤ r⁻¹ := inv_anti₀ hr hzt
        calc |g t| * ((4 * π)⁻¹ * ‖z - t‖⁻¹) ≤ A * ((4 * π)⁻¹ * r⁻¹) := by
              gcongr
              exact hA t
          _ = A * (4 * π)⁻¹ * r⁻¹ := by ring
    · rw [integral_const_mul, FundSol.Internal.integral_ballPow_zero (by linarith)]
      have e : A * (4 * π)⁻¹ * r⁻¹ * (V * (2 * r) ^ 3) = A * ((4 * π)⁻¹ * 8 * V) * r ^ 2 := by
        field_simp
        ring
      rw [e]
      gcongr
      · linarith

end Breakdown.Internal
