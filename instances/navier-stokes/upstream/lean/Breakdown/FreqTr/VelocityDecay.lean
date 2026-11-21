import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.VelocityDecay

theorem weightBound {E : Type*} [NormedAddCommGroup E] {ψ : Space → E} (hcont : Continuous ψ)
    (hc : HasCompactSupport ψ) (k : ℕ) : ∃ A : ℝ, ∀ y, ‖ψ y‖ ≤ A / (1 + ‖y‖) ^ k := by
  have hw : Continuous (fun y : Space => (1 + ‖y‖) ^ k * ‖ψ y‖) :=
    ((continuous_const.add continuous_norm).pow k).mul hcont.norm
  have hcs : HasCompactSupport (fun y : Space => (1 + ‖y‖) ^ k * ‖ψ y‖) := by
    refine hc.mono ?_
    intro y hy h
    apply hy
    simp [h]
  obtain ⟨A, hA⟩ := hw.bounded_above_of_compact_support hcs
  refine ⟨A, fun y => ?_⟩
  have hpos : 0 < (1 + ‖y‖) ^ k := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  have h := hA y
  rwa [Real.norm_of_nonneg (by positivity)] at h

theorem isDecayField_of_isTestField {φ : Space → Space} (hφ : IsTestField φ) :
    IsDecayField φ := by
  obtain ⟨hs, hc, hd⟩ := hφ
  refine ⟨hs, hd, ?_⟩
  obtain ⟨A, hA⟩ := weightBound hs.continuous hc 1
  obtain ⟨B, hB⟩ := weightBound ((contDiff_infty.mp hs 1).continuous_fderiv (by norm_num))
    (hc.fderiv (𝕜 := ℝ)) 2
  refine ⟨max A B, fun y => ⟨?_, ?_⟩⟩
  · have hpos : 0 < 1 + ‖y‖ := by positivity
    have h := hA y
    rw [pow_one] at h
    exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) hpos.le)
  · have hpos : 0 < (1 + ‖y‖) ^ 2 := by positivity
    exact (hB y).trans (div_le_div_of_nonneg_right (le_max_right _ _) hpos.le)

theorem isDecayField_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f - g) := by
  obtain ⟨hfs, hfd, C, hC⟩ := hf
  obtain ⟨hgs, hgd, D, hD⟩ := hg
  have hfdiff : Differentiable ℝ f := (contDiff_infty.mp hfs 1).differentiable (by norm_num)
  have hgdiff : Differentiable ℝ g := (contDiff_infty.mp hgs 1).differentiable (by norm_num)
  have hder : ∀ y, fderiv ℝ (f - g) y = fderiv ℝ f y - fderiv ℝ g y := fun y =>
    fderiv_sub (hfdiff y) (hgdiff y)
  refine ⟨hfs.sub hgs, fun y => ?_, C + D, fun y => ⟨?_, ?_⟩⟩
  · have h1 := hfd y
    have h2 := hgd y
    simp only [divergenceAt] at h1 h2 ⊢
    rw [hder y]
    calc ∑ i : Fin 3, ((fderiv ℝ f y - fderiv ℝ g y) (unitVector i)) i
        = ∑ i : Fin 3, ((fderiv ℝ f y (unitVector i)) i - (fderiv ℝ g y (unitVector i)) i) :=
          Finset.sum_congr rfl fun i _ => rfl
      _ = 0 := by rw [Finset.sum_sub_distrib, h1, h2, sub_zero]
  · rw [add_div]
    calc ‖(f - g) y‖ = ‖f y - g y‖ := rfl
      _ ≤ ‖f y‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ C / (1 + ‖y‖) + D / (1 + ‖y‖) := add_le_add (hC y).1 (hD y).1
  · rw [add_div, hder y]
    exact (norm_sub_le _ _).trans (add_le_add (hC y).2 (hD y).2)

end Internal.VelocityDecay

theorem velocityDecay (h1 : VelocityExists) (_h2 : TestDenseGraph) (h3 : TestDense)
    (h4 : TestSpanSpec) (h5 : EmbedLinear) (h6 : EmbedNorm) (h7 : GradSixDecay) (_h8 : EmbedMem) :
    VelocityDecay := by
  intro f hf
  have hV : VelocitySpec velocity := by
    have hex : ∃ V, VelocitySpec V := h1
    unfold velocity
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨S, hS⟩ := h7
  have hf6 : MemLp f 6 volume := (hS f hf).1
  have key : velocity (embedX f) = hf6.toLp f := by
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set K : ℝ := ‖(velocity : X →L[ℝ] L6R)‖ + |S| + 1 with hKdef
    have hK : 0 < K := by positivity
    obtain ⟨x, hxball, hxs⟩ := Metric.dense_iff.mp h3 (embedX f) (ε / K) (div_pos hε hK)
    obtain ⟨φ, hφ, rfl⟩ := h4 x hxs
    have hφd := Internal.VelocityDecay.isDecayField_of_isTestField hφ
    have hφ6 : MemLp φ 6 volume := (hS φ hφd).1
    have hdiff : IsDecayField (φ - f) := Internal.VelocityDecay.isDecayField_sub hφd hf
    have hb := (hS (φ - f) hdiff).2
    have hn : Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ (φ - f) y (unitVector i)‖ ^ 2) =
        ‖embedX φ - embedX f‖ := by
      rw [← h5.2.1 φ f hφd hf, ← h6 _ hdiff, Real.sqrt_sq (norm_nonneg _)]
    have hL : ‖hφ6.toLp φ - hf6.toLp f‖ = (eLpNorm (φ - f) 6 volume).toReal := by
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
    have hvφ : velocity (embedX φ) = hφ6.toLp φ := by
      rw [hV φ hφ]
      unfold toLpOrZero
      rw [dif_pos hφ6]
    have hd : ‖embedX φ - embedX f‖ < ε / K := by
      rw [← dist_eq_norm]
      exact hxball
    have hd' : ‖embedX f - embedX φ‖ = ‖embedX φ - embedX f‖ := norm_sub_rev _ _
    have hA : ‖velocity (embedX f) - velocity (embedX φ)‖ ≤
        ‖(velocity : X →L[ℝ] L6R)‖ * ‖embedX φ - embedX f‖ := by
      rw [← map_sub, ← hd']
      exact ContinuousLinearMap.le_opNorm _ _
    have hB : ‖hφ6.toLp φ - hf6.toLp f‖ ≤ |S| * ‖embedX φ - embedX f‖ := by
      rw [hL, ← hn]
      refine hb.trans ?_
      rw [hn]
      exact mul_le_mul_of_nonneg_right (le_abs_self S) (norm_nonneg _)
    have hsplit : velocity (embedX f) - hf6.toLp f =
        (velocity (embedX f) - velocity (embedX φ)) + (hφ6.toLp φ - hf6.toLp f) := by
      rw [hvφ]
      abel
    have hKd : K * ‖embedX φ - embedX f‖ ≤ ε := by
      have := (mul_lt_mul_of_pos_left hd hK).le
      rwa [mul_div_cancel₀ _ hK.ne'] at this
    rw [hsplit, zero_add]
    calc _ ≤ ‖velocity (embedX f) - velocity (embedX φ)‖ + ‖hφ6.toLp φ - hf6.toLp f‖ :=
          norm_add_le _ _
      _ ≤ ‖(velocity : X →L[ℝ] L6R)‖ * ‖embedX φ - embedX f‖ + |S| * ‖embedX φ - embedX f‖ :=
          add_le_add hA hB
      _ ≤ K * ‖embedX φ - embedX f‖ := by
          rw [hKdef, ← add_mul]
          exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ ε := hKd
  rw [key]
  exact hf6.coeFn_toLp

end Breakdown.Freq
