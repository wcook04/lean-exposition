import TorusEuler.TerminalScheduledParentJets
import TorusEuler.TerminalStageCoefficientBounds

/-! The old-parent coefficient and residual bounds on the actual selected slab. -/

open Set

namespace TorusEuler.ScheduledEulerConstruction

noncomputable section

private theorem one_add_scale_pow_le {D : ℝ} (hD : 2 ≤ D) (B : ℕ) :
    1 + D * D ^ B ≤ D ^ (B + 2) := by
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hBase : 1 ≤ D * D ^ B := one_le_mul_of_one_le_of_one_le hD₁ (one_le_pow₀ hD₁)
  calc
    _ ≤ 2 * (D * D ^ B) := by linarith only [hBase]
    _ ≤ D * (D * D ^ B) := mul_le_mul_of_nonneg_right hD (zero_le_one.trans hBase)
    _ = _ := by rw [pow_add, pow_two]; ring

/-- The mixed flow amplitude is bounded by a single parent-scale power. -/
theorem exists_scheduledFlowCoefficientPower (q B : ℕ) :
    ∃ E : ℕ, (B + 2) * q ≤ E ∧ ∀ {D : ℝ}, 2 ≤ D →
      terminalFlowTimeAmplitude q D (D ^ B) ≤ D ^ E := by
  let g := B + 1 + (B + 2) * q
  let f := 1 + g * q
  let E₀ := max g (1 + f)
  refine ⟨E₀ + 2, ?_, ?_⟩
  · have h : g ≤ E₀ := le_max_left _ _
    dsimp only [g] at h
    omega
  intro D hD
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hD₀ : 0 ≤ D := zero_le_one.trans hD₁
  let M := D ^ B * D * (1 + D * D ^ B) ^ q
  let G := D * M ^ q
  have hM₀ : 0 ≤ M := by dsimp only [M]; positivity
  have hM : M ≤ D ^ g := by
    dsimp only [M, g]
    rw [pow_add D (B + 1), pow_add D B 1, pow_one, pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (one_add_scale_pow_le hD B) q)
      (by positivity)
  have hG : G ≤ D ^ f := by
    dsimp only [G, f]
    rw [pow_add, pow_one, pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM₀ hM q) hD₀
  have hDp : D * G ≤ D ^ (1 + f) := by rw [pow_add, pow_one]; exact mul_le_mul_of_nonneg_left hG hD₀
  have hgm : D ^ g ≤ D ^ E₀ := pow_le_pow_right₀ hD₁ (le_max_left _ _)
  have hgf : D ^ (1 + f) ≤ D ^ E₀ := pow_le_pow_right₀ hD₁ (le_max_right _ _)
  have hff : D ^ f ≤ D ^ E₀ := (pow_le_pow_right₀ hD₁ (by omega : f ≤ 1 + f)).trans hgf
  change M + G + D * G ≤ D ^ (E₀ + 2)
  calc
    _ ≤ D ^ E₀ + D ^ E₀ + D ^ E₀ :=
      add_le_add (add_le_add (hM.trans hgm) (hG.trans hff)) (hDp.trans hgf)
    _ = 3 * D ^ E₀ := by ring
    _ ≤ D ^ 2 * D ^ E₀ := mul_le_mul_of_nonneg_right
      ((by norm_num : (3 : ℝ) ≤ 2 ^ (2 : ℕ)).trans (pow_le_pow_left₀ zero_le_two hD 2))
      (pow_nonneg hD₀ _)
    _ = _ := by rw [pow_add, mul_comm]

/-- The reciprocal amplitude costs a power fixed by the input exponent and time order. -/
theorem exists_scheduledReciprocalPower (e q : ℕ) :
    ∃ E : ℕ, ∀ {D A : ℝ}, 2 ≤ D → 0 ≤ A → A ≤ D ^ e →
      terminalReciprocalTimeAmplitude A (D ^ 4) q ≤ D ^ E := by
  induction q with
  | zero =>
    exact ⟨4, fun _ _ _ => le_rfl⟩
  | succ q ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨e + 2 * E + 1, ?_⟩
    intro D A hD hA hAe
    let W := terminalReciprocalTimeAmplitude A (D ^ 4) q
    have hD₁ : 1 ≤ D := one_le_two.trans hD
    have hD₀ : 0 ≤ D := zero_le_one.trans hD₁
    have hW₀ : 0 ≤ W := terminalReciprocalTimeAmplitude_nonneg hA (pow_nonneg hD₀ _) q
    have hW : W ≤ D ^ E := hE hD hA hAe
    have hAWW : A * (W * W) ≤ D ^ (e + 2 * E) := by
      rw [pow_add, Nat.mul_comm 2 E, pow_mul, pow_two]
      exact mul_le_mul hAe (mul_le_mul hW hW hW₀ (pow_nonneg hD₀ _))
        (mul_nonneg hW₀ hW₀) (pow_nonneg hD₀ _)
    have hW' : W ≤ D ^ (e + 2 * E) :=
      hW.trans (pow_le_pow_right₀ hD₁ (by omega))
    change W + A * (W * W) ≤ D ^ (e + 2 * E + 1)
    rw [pow_add, pow_one]
    calc
      _ ≤ D ^ (e + 2 * E) + D ^ (e + 2 * E) := add_le_add hW' hAWW
      _ = D ^ (e + 2 * E) * 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (pow_nonneg hD₀ _)

variable {P : InductiveEulerParameters}

/-- The transported carrier normalized at the launch frequency of the
selected child wave. -/
abbrev scheduledParentCovector (c : ScheduledEulerConstruction P) (n : ℕ) : Velocity :=
  fun t x => (P.frequency (n + 2))⁻¹ •
    labelWaveVector (c.construction.tip n).parent.flow 0 x (c.selectedStep n).selected.carrier t

/-- Actual time and space estimates for the coefficients in the selected
hierarchy. One exponent and one order function control the coefficients
and the old residual while retaining the latter's smallness. -/
structure ScheduledParentCoefficientTimeBounds (c : ScheduledEulerConstruction P) (n q E : ℕ)
    (C : ℕ → ℝ) : Prop where
  forward : TerminalMixedJetBound 0 (c.construction.slab (n + 2)) (q + 1) 16
    (P.frequency (n + 1) ^ 9) ((P.frequency (n + 1) ^ 9) ^ E) C
    (fun t x => fderiv ℝ ((c.construction.tip n).parent.flow 0 t) x)
  inverse : TerminalMixedJetBound 0 (c.construction.slab (n + 2)) (q + 1) 16
    (P.frequency (n + 1) ^ 9) ((P.frequency (n + 1) ^ 9) ^ E) C
    (fun t x => fderiv ℝ ((c.construction.tip n).parent.flow t 0)
      ((c.construction.tip n).parent.flow 0 t x))
  gradient : TerminalMixedJetBound 0 (c.construction.slab (n + 2)) (q + 1) 16
    (P.frequency (n + 1) ^ 9) ((P.frequency (n + 1) ^ 9) ^ E) C
    (fun t x => fderiv ℝ ((c.construction.tip n).parent.velocity t)
      ((c.construction.tip n).parent.flow 0 t x))
  covector : TerminalMixedJetBound 0 (c.construction.slab (n + 2)) (q + 1) 16
    (P.frequency (n + 1) ^ 9) ((P.frequency (n + 1) ^ 9) ^ E) C (c.scheduledParentCovector n)
  reciprocal : TerminalMixedJetBound 0 (c.construction.slab (n + 2)) (q + 1) 16
    (P.frequency (n + 1) ^ 9) ((P.frequency (n + 1) ^ 9) ^ E) C
    (fun t x => (‖c.scheduledParentCovector n t x‖ ^ 2)⁻¹)
  residual : TerminalMixedJetBound 0 (c.construction.slab (n + 2)) q 16
    (P.frequency (n + 1) ^ 9)
    (((P.frequency (n + 1) ^ 9) ^ E) * P.frequency (n + 2) ^ (-(5 / 2) : ℝ)) C
    (fun t x => (c.construction.tip n).parent.residual t ((c.construction.tip n).parent.flow 0 t x))

set_option maxHeartbeats 2000000 in
/-- The scheduled parent time bounds supply all raw coefficient jets and
the pulled-back old residual of the exact selected child hierarchy. -/
theorem exists_scheduledParentCoefficientTimeBounds (q A : ℕ) :
    ∃ (E : ℕ) (C : ℕ → ℝ), (∀ m, 0 ≤ C m) ∧
      ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (n : ℕ),
        2 ≤ P.frequency (n + 1) → c.construction.stages.StageTimeBounds q A (n + 1) →
        c.ScheduledParentCoefficientTimeBounds n q E C := by
  obtain ⟨B, K, _, hK, hParent⟩ := exists_scheduledParentMixedJetBounds q A
  obtain ⟨C, Ci, hC, hCi, hCoefficients⟩ :=
    InductiveEulerStage.OnSlab.exists_terminalStageCoefficientBounds K hK (q + 1)
  obtain ⟨Cr, hCr, hResidual⟩ :=
    InductiveEulerStage.OnSlab.exists_terminalStageResidualPullbackBounds K K hK hK q
  obtain ⟨E₁, hE₁, hFlowPower⟩ := exists_scheduledFlowCoefficientPower (q + 1) B
  obtain ⟨E₂, hRecPower⟩ := exists_scheduledReciprocalPower (2 * E₁) (q + 1)
  let E := max E₁ E₂
  let Ctot (m : ℕ) := C m + Ci m + Cr m
  refine ⟨E, Ctot, fun m => add_nonneg (add_nonneg (hC m) (hCi m)) (hCr m), ?_⟩
  intro P c n hParentFreq hTime
  let tip := c.construction.tip n
  let d := (c.selectedStep n).selected
  let μ := P.frequency (n + 1)
  let ν := P.frequency (n + 2)
  let D := μ ^ (9 : ℕ)
  let A₀ := D ^ B
  let T := c.construction.slab (n + 2)
  let cap := terminalFlowTimeAmplitude (q + 1) D A₀
  have hμ : 1 ≤ μ := one_le_two.trans hParentFreq
  have hμ₀ : 0 ≤ μ := zero_le_one.trans hμ
  have hD₂ : 2 ≤ D := (by norm_num : (2 : ℝ) ≤ 2 ^ (9 : ℕ)).trans
    (pow_le_pow_left₀ zero_le_two hParentFreq _)
  have hD : 1 ≤ D := one_le_two.trans hD₂
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hA₀ : 1 ≤ A₀ := one_le_pow₀ hD
  have hμD : μ ≤ D := le_self_pow₀ hμ (by decide : (9 : ℕ) ≠ 0)
  have hν : 0 < ν := zero_lt_one.trans_le d.child_frequency_ge_one
  have hR₀ : 0 ≤ ν ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg hν.le _
  obtain ⟨hUraw, hRraw⟩ := hParent c n hParentFreq hTime
  have hU : TerminalMixedJetBound 0 T (q + 1) 1 D A₀ K tip.parent.velocity := by
    have h₁ := TerminalMixedJetBound.of_parentBernstein hμ (pow_nonneg hμ₀ B) hK hUraw
    exact h₁.mono_amplitude hD₀ hK (pow_le_pow_left₀ hμ₀ hμD B)
  have hR : TerminalMixedJetBound 0 T q 1 D (ν ^ (-(5 / 2) : ℝ)) K tip.parent.residual :=
    TerminalMixedJetBound.of_parentBernstein hμ hR₀ hK hRraw
  obtain ⟨hF, hG, hM, hκ, hι⟩ := hCoefficients (A := A₀) d.parent d.time_le_one hParentFreq
    hA₀ hν d.launch_time_mem d.label_launch_covector_norm hU
  have hRR : TerminalMixedJetBound 0 T q 6 D (ν ^ (-(5 / 2) : ℝ) * (1 + D * A₀)^q) Cr
      (fun t x => tip.parent.residual t (tip.parent.flow 0 t x)) := by
    have hR' : TerminalMixedJetBound 0 T q 1 D (ν ^ (-5 / 2 : ℝ)) K tip.parent.residual := by
      simpa only [neg_div] using hR
    have h := hResidual (A := A₀) d.parent d.time_le_one hParentFreq
      (zero_le_one.trans hA₀) (hU.mono_order (Nat.le_succ q)) hR'
    change TerminalMixedJetBound 0 T q 6 D (ν ^ (-5 / 2 : ℝ) * (1 + D * A₀)^q) Cr
      (fun t x => tip.parent.residual t (tip.parent.flow 0 t x)) at h
    simpa only [neg_div] using h
  have hCap₀ : 0 ≤ cap := by dsimp only [cap, terminalFlowTimeAmplitude]; positivity
  have hCap : cap ≤ D ^ E₁ := hFlowPower hD₂
  have hCapE : cap ≤ D ^ E := hCap.trans (pow_le_pow_right₀ hD (le_max_left _ _))
  have hCapSq : cap * cap ≤ D ^ (2 * E₁) := by
    rw [Nat.mul_comm 2 E₁, pow_mul, pow_two]
    exact mul_le_mul hCap hCap hCap₀ (pow_nonneg hD₀ _)
  have hRecE : terminalReciprocalTimeAmplitude (cap * cap) (D ^ 4) (q + 1) ≤ D ^ E :=
    (hRecPower hD₂ (mul_nonneg hCap₀ hCap₀) hCapSq).trans
      (pow_le_pow_right₀ hD (le_max_right _ _))
  have hResE : ν ^ (-(5 / 2) : ℝ) * (1 + D * A₀)^q ≤
      D ^ E * ν ^ (-(5 / 2) : ℝ) := by
    rw [mul_comm (D ^ E)]
    apply mul_le_mul_of_nonneg_left _ hR₀
    refine (pow_le_pow_left₀ (by positivity) (one_add_scale_pow_le hD₂ B) q).trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ hD
      ((Nat.mul_le_mul_left (B + 2) (Nat.le_succ q)).trans (hE₁.trans (le_max_left _ _)))
  have hCost (m : ℕ) : C m ≤ Ctot m := by dsimp only [Ctot]; linarith [hCi m, hCr m]
  have hCostI (m : ℕ) : Ci m ≤ Ctot m := by dsimp only [Ctot]; linarith [hC m, hCr m]
  have hCostR (m : ℕ) : Cr m ≤ Ctot m := by dsimp only [Ctot]; linarith [hC m, hCi m]
  have hAmp : 0 ≤ D ^ E := pow_nonneg hD₀ _
  have hAmpR : 0 ≤ D ^ E * ν ^ (-(5 / 2) : ℝ) := mul_nonneg hAmp hR₀
  exact
    ⟨(hF.mono_amplitude hD₀ hC hCapE).mono_constant hD₀ hAmp hCost,
      (hG.mono_amplitude hD₀ hC hCapE).mono_constant hD₀ hAmp hCost,
      (hM.mono_amplitude hD₀ hC hCapE).mono_constant hD₀ hAmp hCost,
      (hκ.mono_amplitude hD₀ hC hCapE).mono_constant hD₀ hAmp hCost,
      (hι.mono_amplitude hD₀ hCi hRecE).mono_constant hD₀ hAmp hCostI,
      (((hRR.mono_amplitude hD₀ hCr hResE).mono_slope hD hAmpR hCr
        (by decide : 6 ≤ 16)).mono_constant hD₀ hAmpR hCostR)⟩

end

end TorusEuler.ScheduledEulerConstruction
