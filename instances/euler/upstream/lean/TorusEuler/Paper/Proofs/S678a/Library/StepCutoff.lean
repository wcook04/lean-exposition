import TorusEuler.Paper.Proofs.S678a.Library.StepBundle
import TorusEuler.PaperGenericPhysicalResidual
import TorusEuler.InductiveWaveSwitchBound

/-! # The cutoff of a later wave and the residual size (package S678a)

Items 4-5 of the proof of Theorem 7.1 (sections/08b_induction.tex:376-461): the cutoff `χ̃_j` of the
expansion is `waveSwitch t_j r_j` (Section 7, sections/08b_induction.tex:94-140), and the
weighted size `‖χ̃_j' γ‖` that enters the residual bound of Lemma 5.8 is bounded by (6.8)
(`early_gain`), `μ λ_{j+1}^{-4}`. -/

open Set

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- The cutoff `waveSwitch t₀ r` as a `PaperWaveCutoff` (smooth, in `[0,1]`, zero before `t₀`). -/
def paperCutoffOfWaveSwitch (t₀ r T : ℝ) (hr : 0 ≤ r) : PaperWaveCutoff t₀ T where
  value := waveSwitch t₀ r
  smooth := (contDiff_waveSwitch t₀ r).contDiffOn
  range := fun _ _ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  zero_before := fun _ _ ht => waveSwitch_eq_zero_of_le hr ht.le

/-- The derivative of the cutoff `paperCutoffOfWaveSwitch` is the derivative of `waveSwitch t₀ r` on `[0,T]`. -/
theorem paperCutoffOfWaveSwitch_derivative {t₀ r T : ℝ} (hr : 0 ≤ r) (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Icc 0 T) : (paperCutoffOfWaveSwitch t₀ r T hr).derivative t =
      deriv (waveSwitch t₀ r) t :=
  ((contDiff_waveSwitch t₀ r).differentiable (by simp) t).derivWithin (uniqueDiffOn_Icc hT t ht)

/-- The weighted derivative size of the switch is at most the pointwise bound. -/
theorem derivativeSize_paperCutoffOfWaveSwitch_le {t₀ r T M : ℝ} (hr : 0 ≤ r) (hT : 0 < T)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ) (hγ : ∀ t ∈ Icc t₀ T, 0 ≤ γ t)
    (h : ∀ t, |deriv (waveSwitch t₀ r) t| * |γ t| ≤ M) :
    (paperCutoffOfWaveSwitch t₀ r T hr).derivativeSize γ ≤ M := by
  have : Nonempty (Icc t₀ T) := ⟨⟨t₀, le_rfl, htT⟩⟩
  refine ciSup_le fun t => ?_
  have ht : (t : ℝ) ∈ Icc 0 T := ⟨ht₀.trans t.2.1, t.2.2⟩
  rw [paperCutoffOfWaveSwitch_derivative hr hT ht]
  have := h t
  rwa [abs_of_nonneg (hγ _ t.2)] at this

/-- The residual size of Lemma 5.8 (the product `Γ D^b λ² (λ^{-2P/3} + ‖χ̃'γ‖)`) is at most
`λ_{j+1}^{-7/2}` from the schedule (`step_rate_mul_parent`, `residual_rate`) and
`‖χ̃'γ‖ ≤ μ λ_{j+1}^{-4}`. -/
theorem residual_size_of_budget {X μ lam nxt dS : ℝ} {K : ℕ}
    (hμ : 1 ≤ μ) (hX : 0 ≤ X) (hlam : 1 ≤ lam) (hdS : dS ≤ μ * nxt ^ (-4 : ℝ))
    (hnxt : nxt = lam ^ K) (hrate : X * μ ≤ lam ^ (1 / 16 : ℝ))
    (hres : 2 * lam ^ (2 + 1 / 16 : ℝ) * nxt ^ (-4 : ℝ) ≤ nxt ^ (-7 / 2 : ℝ)) :
    X * lam ^ (2 : ℝ) * (lam ^ (-2 * (6 * (K : ℝ)) / 3) + dS) ≤ nxt ^ (-7 / 2 : ℝ) := by
  have hl0 : 0 < lam := zero_lt_one.trans_le hlam
  have hn0 : 0 < nxt := by rw [hnxt]; positivity
  have hpow : lam ^ (-2 * (6 * (K : ℝ)) / 3) = nxt ^ (-4 : ℝ) := by
    rw [hnxt, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
    congr 1
    ring
  rw [hpow]
  have h1 : nxt ^ (-4 : ℝ) + dS ≤ 2 * μ * nxt ^ (-4 : ℝ) := by
    have hp : 0 ≤ nxt ^ (-4 : ℝ) := by positivity
    nlinarith
  calc X * lam ^ (2 : ℝ) * (nxt ^ (-4 : ℝ) + dS)
      ≤ X * lam ^ (2 : ℝ) * (2 * μ * nxt ^ (-4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * (X * μ) * lam ^ (2 : ℝ) * nxt ^ (-4 : ℝ) := by ring
    _ ≤ 2 * lam ^ (1 / 16 : ℝ) * lam ^ (2 : ℝ) * nxt ^ (-4 : ℝ) := by
        gcongr
    _ = 2 * lam ^ (2 + 1 / 16 : ℝ) * nxt ^ (-4 : ℝ) := by
        rw [add_comm, Real.rpow_add hl0]; ring
    _ ≤ _ := hres

end

end TorusEuler.Paper.Lib.S678a
