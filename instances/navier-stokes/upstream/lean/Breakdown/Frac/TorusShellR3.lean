import Breakdown.Frac.StTorusShell
import Breakdown.Torus.ShellR3
import Breakdown.FreqTr.Realization
import Breakdown.Frac.RBilinTestCompact

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Internal.FracShellR3

open Internal.ShellR3

theorem sqrt_fracPhi_product {α K τ s : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hτ : 0 < τ) (hs : 0 ≤ s) :
    Real.sqrt ((K * τ ^ (-(1 / (2 * α))) * s) * (K * τ ^ (-(1 / α)) * s)) =
      K * τ ^ (-(3 / (4 * α))) * s := by
  have e : (τ ^ (-(3 / (4 * α)))) ^ 2 = τ ^ (-(1 / (2 * α))) * τ ^ (-(1 / α)) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    congr 1
    field_simp
    ring
  rw [show (K * τ ^ (-(1 / (2 * α))) * s) * (K * τ ^ (-(1 / α)) * s) =
      (K * τ ^ (-(3 / (4 * α))) * s) ^ 2 by rw [mul_pow, mul_pow, e]; ring]
  exact Real.sqrt_sq (by positivity)

set_option maxHeartbeats 400000 in
theorem inner_fracHeatSolenoidal_le {α : ℝ} (hα : 1 < α) (hPhi : Freq.FracPhiBounds α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → ∀ ζ : ShellData,
      ∀ ψ : Freq.X, inner ℝ (Freq.fracHeatSolenoidal α τ (advectShell φ hφ b ζ)) ψ ≤
        C * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖ζ‖ * ‖ψ‖ := by
  have hVs : Freq.VelocityDecay := Freq.velocityDecay_holds
  have hPd : Freq.PartialDecay := Freq.partial_holds.1
  have hP : Freq.PartialNormLe := Freq.partial_holds.2
  have hα0 : 0 < α := by linarith
  obtain ⟨C0, hC0⟩ := hPhi
  obtain ⟨K, hK_def⟩ : ∃ K, K = |C0| := ⟨_, rfl⟩
  have hK : 0 ≤ K := hK_def ▸ abs_nonneg C0
  obtain ⟨V, hV_def⟩ : ∃ V, V = ‖(Freq.velocity : Freq.X →L[ℝ] Freq.L6R)‖ := ⟨_, rfl⟩
  have hV : 0 ≤ V := hV_def ▸ norm_nonneg _
  refine ⟨3 * (V + 1) * K, mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hK, ?_⟩
  intro φ hφ b τ hτ ζ ψ
  obtain ⟨hw6, hw2, hw6'⟩ := hC0 τ hτ ψ
  have hD := Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ
  have hAeq : advectShell φ hφ b ζ = advectShellFun φ b ζ := rfl
  rw [hAeq]
  obtain ⟨A, hA_def⟩ : ∃ A, A = advectShellFun φ b ζ := ⟨_, rfl⟩
  rw [← hA_def]
  obtain ⟨e, he_def⟩ : ∃ e, e = Freq.embedX φ := ⟨_, rfl⟩
  rw [← he_def]
  obtain ⟨w, hw_def⟩ : ∃ w, w = Freq.fracPhiX α τ ψ := ⟨_, rfl⟩
  rw [← hw_def] at hw6 hw2 hw6'
  obtain ⟨P, hP_def⟩ : ∃ P, P = Freq.velocity e := ⟨_, rfl⟩
  have hc0 : 0 ≤ K * τ ^ (-(1 / (2 * α))) * ‖ψ‖ :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hτ.le _)) (norm_nonneg ψ)
  have hd0 : 0 ≤ K * τ ^ (-(1 / α)) * ‖ψ‖ :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hτ.le _)) (norm_nonneg ψ)
  have hVe : 0 ≤ V * ‖e‖ := mul_nonneg hV (norm_nonneg e)
  have hw2' : eLpNorm (w : Space → Space) 2 volume ≤
      ENNReal.ofReal (K * τ ^ (-(1 / (2 * α))) * ‖ψ‖) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (Lp.memLp w).eLpNorm_ne_top hc0]
    refine hw2.trans ?_
    rw [hK_def]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.rpow_nonneg hτ.le _)) (norm_nonneg ψ)
  have hw6'' : eLpNorm (w : Space → Space) 6 volume ≤
      ENNReal.ofReal (K * τ ^ (-(1 / α)) * ‖ψ‖) := by
    rw [ENNReal.le_ofReal_iff_toReal_le hw6.eLpNorm_ne_top hd0]
    refine hw6'.trans ?_
    rw [hK_def]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.rpow_nonneg hτ.le _)) (norm_nonneg ψ)
  have hsq := sqrt_fracPhi_product hα0 hK hτ (norm_nonneg ψ)
  have hPφ : (P : Space → Space) =ᵐ[volume] φ := by
    rw [hP_def, he_def]
    exact hVs φ hD
  have hQφ : ∀ᵐ y ∂volume, ∀ j : Fin 3,
      (Freq.partialX j e : Space → Space) y = Freq.partialField φ j y := by
    rw [ae_all_iff, he_def]
    exact fun j => hPd φ hD j
  have hA : ∀ᵐ y ∂volume, ‖(A : Space → Space) y‖ ≤
      ‖(Metric.closedBall (0 : Space) b).indicator
        (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
          (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) y‖ := by
    rw [hA_def]
    exact toLpOrZero_norm_le 2 _
  have hpt : ∀ᵐ y ∂volume, ENNReal.ofReal ‖inner ℝ ((A : Space → Space) y) (w y)‖ ≤
      ∑ j : Fin 3, (ENNReal.ofReal (‖(P : Space → Space) y‖ * ‖(ζ.1 j : Space → Space) y‖ * ‖w y‖) +
        ENNReal.ofReal (‖(ζ.2 : Space → Space) y‖ * ‖(Freq.partialX j e : Space → Space) y‖ *
          ‖w y‖)) := by
    filter_upwards [hPφ, hQφ, hA] with y hy1 hy2 hy3
    exact pointwise_inner_le _ _ _ _ _ _ _ _ hy1 hy2 (hy3.trans (norm_indicator_le_norm_self _ _))
  rw [FracInternal.fracHeatProject_inner hα hτ, ← hw_def, MeasureTheory.L2.inner_def]
  have hI := integral_bound_of_parts A w P ζ.2 ζ.1 (fun j => Freq.partialX j e) hVe (norm_nonneg ζ)
    (norm_nonneg e) hc0 hd0 (by rw [hP_def, hV_def]; exact Freq.velocity.le_opNorm e)
    (fun j => (norm_le_pi_norm ζ.1 j).trans (norm_fst_le ζ)) (norm_snd_le ζ)
    (fun j => partialX_norm_le hP e j) hw2' hw6'' hpt
  rw [hsq] at hI
  have key : 3 * (V * ‖e‖ * ‖ζ‖ * (K * τ ^ (-(3 / (4 * α))) * ‖ψ‖) +
      ‖ζ‖ * ‖e‖ * (K * τ ^ (-(3 / (4 * α))) * ‖ψ‖)) =
      3 * (V + 1) * K * τ ^ (-(3 / (4 * α))) * ‖e‖ * ‖ζ‖ * ‖ψ‖ := by ring
  exact hI.trans key.le

end Internal.FracShellR3

open Internal.ShellR3 in
theorem fracR3Factor (α : ℝ) (_hα : 1 < α) (h1 : Freq.FracBilinTestFormula α) : FracR3Factor α := by
  intro φ hφ b hb τ hτ v
  rw [h1 φ hφ τ hτ v, fracLambdaR3]
  show _ = -(Freq.fracHeatSolenoidal α τ (advectShell φ hφ b (restrictR3 b v)))
  rw [advectShell_restrict hφ hb, smul_smul, show (2 : ℝ) * (-(1 / 2)) = -1 by norm_num, neg_one_smul]

open Internal.FracShellR3 in
theorem fracR3LambdaBound (α : ℝ) (hα : 1 < α) (h1 : Freq.FracPhiBounds α) : FracR3LambdaBound α := by
  obtain ⟨C, hC, hI⟩ := inner_fracHeatSolenoidal_le hα h1
  refine ⟨C, hC, fun φ hφ b τ hτ ζ => ?_⟩
  have hx : ‖fracLambdaR3 α φ hφ b τ ζ‖ = ‖Freq.fracHeatSolenoidal α τ (advectShell φ hφ b ζ)‖ := by
    rw [fracLambdaR3]
    show ‖-(Freq.fracHeatSolenoidal α τ (advectShell φ hφ b ζ))‖ = _
    rw [norm_neg]
  rw [hx]
  have h2 := hI φ hφ b τ hτ ζ (Freq.fracHeatSolenoidal α τ (advectShell φ hφ b ζ))
  rw [real_inner_self_eq_norm_sq] at h2
  have hM : 0 ≤ C * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖ζ‖ := by
    have : 0 < τ ^ (-(3 / (4 * α))) := Real.rpow_pos_of_pos hτ _
    positivity
  nlinarith [norm_nonneg (Freq.fracHeatSolenoidal α τ (advectShell φ hφ b ζ))]

end Breakdown.Periodic
