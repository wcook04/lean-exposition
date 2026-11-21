import Breakdown.Frac.ScaledStatements
import Breakdown.Transfer.ProfilePiece

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {κ : ℝ}

theorem scaledProfilePiece_apply (h1 : ScaledOrbitPhysicalStatement) (hκ : 0 < κ)
    (F : ScaledMildFramework X κ) {ρ : X ≃ₗᵢ[ℝ] X}
    {w : ℝ → X} {P : ℝ} (hw : F.IsOrbit ρ w P) (k m : ℕ)
    (t : Icc (0 : ℝ) (MildFramework.stepLength P k)) :
    F.profilePiece w P k m t = F.selfSimilar w (m * (P / k)) t := by
  have hmild := h1 X κ hκ F w hw.cont hw.flow (m * (P / k))
  have hcont : ContinuousOn (F.selfSimilar w (m * (P / k)))
      (Icc 0 (MildFramework.stepLength P k)) :=
    hmild.1.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 (ProfilePiece.Internal.stepLength_lt_one P k)⟩
  exact ProfilePiece.Internal.toPiece_apply hcont t

theorem scaledExtendPiece_profilePiece (h1 : ScaledOrbitPhysicalStatement) (hκ : 0 < κ)
    (F : ScaledMildFramework X κ)
    {ρ : X ≃ₗᵢ[ℝ] X} {w : ℝ → X} {P : ℝ} (hw : F.IsOrbit ρ w P) {k : ℕ} (hk : 0 < k) (m : ℕ)
    (t : ℝ) (ht : t ∈ Icc 0 (MildFramework.stepLength P k)) :
    extendPiece (F.profilePiece w P k m) t = F.selfSimilar w (m * (P / k)) t := by
  have hL := (ProfilePiece.Internal.stepLength_pos hw.pos hk).le
  unfold extendPiece
  rw [dif_pos hL, IccExtend_of_mem _ _ ht]
  exact scaledProfilePiece_apply h1 hκ F hw k m ⟨t, ht⟩

end FracInternal

open ProfilePiece.Internal FracInternal in
theorem scaledProfilePiece_of (h1 : ScaledOrbitPhysicalStatement) : ScaledProfilePieceStatement := by
  intro X _ _ _ κ hκ F ρ hρ w P hw k hk n
  have hL := stepLength_pos hw.pos hk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have happ := scaledProfilePiece_apply h1 hκ F hw k
  have hext := scaledExtendPiece_profilePiece h1 hκ F hw hk
  refine ⟨happ n, ?_, ?_, ?_, ?_⟩
  · have hmild := h1 X κ hκ F w hw.cont hw.flow (n * (P / k))
    refine ⟨hmild.1.mono (fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 (stepLength_lt_one P k)⟩)
      |>.congr (fun s hs => hext n s hs), ?_⟩
    intro t ht
    have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_lt ht.2 (stepLength_lt_one P k)⟩
    obtain ⟨hi, he⟩ := hmild.2 t ht'
    have heq : EqOn (fun s => F.K (t - s) (F.selfSimilar w (n * (P / k)) s)
        (F.selfSimilar w (n * (P / k)) s))
        (fun s => F.K (t - s) (extendPiece (F.profilePiece w P k n) s)
          (extendPiece (F.profilePiece w P k n) s)) (uIcc 0 t) := by
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hs' : s ∈ Icc 0 (MildFramework.stepLength P k) := ⟨hs.1, hs.2.trans ht.2⟩
      simp only [hext n s hs']
    refine ⟨hi.congr (heq.mono uIoc_subset_uIcc), ?_⟩
    rw [hext n t ht, hext n 0 ⟨le_rfl, hL.le⟩, ← intervalIntegral.integral_congr heq]
    exact he
  · have hend : pieceEnd (MildFramework.stepLength P k) (F.profilePiece w P k n) =
        F.profilePiece w P k n ⟨MildFramework.stepLength P k, hL.le, le_rfl⟩ := by
      unfold pieceEnd
      rw [dif_pos hL.le]
      rfl
    rw [hend, happ, hext (n + 1) 0 ⟨le_rfl, hL.le⟩]
    simp only [ScaledMildFramework.selfSimilar, one_sub_stepLength, Real.log_exp, sub_zero,
      inv_one, Real.log_one, F.D_one, ContinuousLinearMap.id_apply]
    rw [← ContinuousLinearMap.comp_apply, ← F.D_mul _ _ (Real.exp_pos _)
      (inv_pos.mpr (Real.exp_pos _)), mul_inv_cancel₀ (Real.exp_ne_zero _), F.D_one,
      ContinuousLinearMap.id_apply]
    congr 1
    push_cast
    ring
  · intro t
    rw [happ, happ]
    simp only [ScaledMildFramework.selfSimilar]
    have harg : ((n + k : ℕ) : ℝ) * (P / k) - Real.log (1 - t) =
        (n * (P / k) - Real.log (1 - t)) + P := by
      push_cast
      field_simp
      ring
    rw [harg, hw.periodic, hρ.comm_D]
  · intro M hM
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    refine (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le hM0)).mpr ?_
    intro t
    rw [happ]
    have h1t : Real.exp (-(P / k)) ≤ 1 - (t : ℝ) := by
      rw [← one_sub_stepLength]
      linarith [t.2.2]
    have hpos : 0 < 1 - (t : ℝ) := lt_of_lt_of_le (Real.exp_pos _) h1t
    simp only [ScaledMildFramework.selfSimilar]
    rw [F.D_norm _ (inv_pos.mpr hpos)]
    have hinv : (1 - (t : ℝ))⁻¹ ≤ Real.exp (P / k) := by
      have := inv_anti₀ (Real.exp_pos _) h1t
      rwa [← Real.exp_neg, neg_neg] at this
    have hr : ((1 - (t : ℝ))⁻¹) ^ κ ≤ Real.exp (κ * (P / k)) := by
      calc ((1 - (t : ℝ))⁻¹) ^ κ ≤ (Real.exp (P / k)) ^ κ :=
            Real.rpow_le_rpow (inv_pos.mpr hpos).le hinv hκ.le
        _ = Real.exp (κ * (P / k)) := by
            rw [← Real.exp_mul, mul_comm]
    exact mul_le_mul hr (hM _) (norm_nonneg _) (Real.exp_pos _).le

end Breakdown
