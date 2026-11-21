import TorusEuler.InductiveStepNumericalBudgets
import TorusEuler.ScheduleExistence
import TorusEuler.Paper.S678.Statements
import TorusEuler.Paper.Proofs.S678a.Library.Lifetime

/-! # Numerical budget and parameters for an arbitrary admissible threshold (package S678a)

Own glue of row 7.1 (sections/08b_induction.tex:238-248, the parameter choice (1.13)-(1.14) and
`cc:par:step`). `Lib.S678a.stepNumericalBudget_of_threshold_le` is a copy of
`InductiveEulerParameters.stepNumericalBudget_of_threshold` in which the threshold of the
parameters only has to dominate the fixed-order majorant (`F(s) ≤ 𝓑(s)` of
`AdmissibleThreshold`) instead of being equal to it. `Lib.S678a.exists_parameters_of_threshold`
replaces `InductiveEulerParameters.exists_of_fixedOrderCosts`: it builds the parameter record with
`threshold = 𝓑` for any admissible `𝓑` from `frequencySchedule_exists` (it does not use the
library lemmas that carry the content of Lemma 1.3). -/

open Set

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler TorusEuler.InductiveEulerParameters

noncomputable section

/-- Copy of the library's private `stepSmall_of_rate`: `C ≤ λ^{1/32}` gives `Cλ^{-1/12} ≤ 1`. -/
theorem stepSmall_of_rate {freq C : ℝ} (hf : 1 ≤ freq)
    (hC : C ≤ freq ^ (1 / 32 : ℝ)) : C * freq ^ (-1 / 12 : ℝ) ≤ 1 := by
  calc
    _ ≤ freq ^ (1 / 32 : ℝ) * freq ^ (-1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = freq ^ (-5 / 96 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hf)]
      norm_num
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hf (by norm_num)

set_option maxHeartbeats 1200000 in
/-- Copy of `InductiveEulerParameters.stepNumericalBudget_of_threshold` (own glue of row 7.1, the
arithmetic of (7.8) and `cc:par:step`, sections/08b_induction.tex:238-248) for any threshold `P.threshold`
above the fixed-order majorant: the only change is `hThreshold`, whose only use is `hThresholdLe`. -/
theorem stepNumericalBudget_of_threshold_le {ι : Type*} [Fintype ι]
    (P : InductiveEulerParameters) (cost : StepCosts ι) (cutoffConstant : ℝ)
    (hThreshold : ∀ s : ℕ, 1 ≤ s → fixedOrderThreshold P.exponentParameter cost.table s ≤ P.threshold s)
    {a p r absolutePower : ℕ}
    (hb : stepExponentFloor a p r absolutePower ≤ P.exponentParameter)
    (hZero : max 2 ((2 * cutoffConstant) ^ (2 : ℕ)) ≤ P.frequency 0)
    (hGamma : ∀ depth, 1 ≤ cost.step depth) (i : ℕ) :
    P.StepNumericalBudget i a p r absolutePower cutoffConstant cost := by
  let b := P.exponentParameter
  let depth := P.stepDepth i
  let μ := P.frequency i
  let freq := P.frequency (i + 1)
  let D := μ ^ (9 : ℕ)
  have hInitial : 2 ≤ P.frequency 0 := (le_max_left _ _).trans hZero
  have hMono := frequencySchedule_frequency_mono b P.order P.frequency P.exponentParameter_ge
    (one_le_two.trans hInitial) P.frequency_step
  have hμ : 2 ≤ μ := hInitial.trans (hMono (Nat.zero_le i))
  have hfreq : 2 ≤ freq := hInitial.trans (hMono (Nat.zero_le _))
  have hμ₁ : 1 ≤ μ := one_le_two.trans hμ
  have hD : 1 ≤ D := one_le_pow₀ hμ₁
  have hOrder := (frequencySchedule_order_steps P.threshold P.frequency P.order P.initial_order
    P.initial_threshold hMono P.order_maximum i).1
  have hOrderK : P.order (i + 2) + 1 ≤
      frequencyExponent P.exponentParameter (P.order (i + 2)) := by
    unfold frequencyExponent
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) P.exponentParameter_ge)
  have hDepth : max 2 (P.order (i + 1)) ≤ depth := by
    dsimp only [depth, stepDepth]
    exact max_le (by omega) (by omega)
  have hDepthThreshold : depth + 1 ≤
      7 * frequencyExponent P.exponentParameter (P.order (i + 2)) := by
    dsimp only [depth, stepDepth]
    omega
  have hThresholdLe : fixedOrderThreshold b cost.table (P.order (i + 2)) ≤ μ := by
    exact (hThreshold _ (P.order_maximum i).1.1).trans (P.order_maximum i).1.2.2
  have hTable (j : StepCostIndex ι) (m : ℕ) (hm : m ≤ depth + 1) :
      |cost.table j m depth| ≤ μ :=
    (abs_fixedOrderCost_le_threshold b cost.table j (hm.trans hDepthThreshold)
      ((Nat.le_succ depth).trans hDepthThreshold)).trans hThresholdLe
  have hAnalytic (j : ι) (m : ℕ) (hm : m ≤ (depth + 1) + 3 * depth) :
      |cost.analytic j m depth| ≤ μ := by
    have h := hTable (.analytic j) (depth + 1) le_rfl
    change |(∑ n ∈ Finset.range (depth + 1 + 3 * depth + 1), |cost.analytic j n depth|)| ≤ μ at h
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact (Finset.single_le_sum (fun n _ => abs_nonneg (cost.analytic j n depth))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).trans h
  have hCutoff : cost.cutoffTail depth ≤ μ :=
    (le_abs_self _).trans (hTable .cutoffTail 0 (Nat.zero_le _))
  have hStep : cost.step depth ≤ μ := (le_abs_self _).trans (hTable .step 0 (Nat.zero_le _))
  have hMean (m : ℕ) (hm : m ≤ depth + 1) : cost.mean m depth ≤ μ :=
    (le_abs_self _).trans (hTable .mean m hm)
  have hbProfile : max a 1 + (max a 1 + p) + 1 ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hb))
  have hbRadius : a + 1 ≤ b := by
    have ha : a ≤ max a 1 := le_max_left _ _
    omega
  have hbLoss : 6 * r ≤ b :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hb))
  have hbAbsolute : absolutePower ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hb)
  have hfStep : freq = μ ^ frequencyExponent b (P.order (i + 1)) := P.frequency_step i
  have hNextStep : P.frequency (i + 2) = freq ^ frequencyExponent b (P.order (i + 2)) :=
    P.frequency_step (i + 1)
  obtain ⟨hRate₁, hRate₂, hRate₃⟩ := frequencySchedule_step_constant_budget
    (q := P.order (i + 1)) P.exponentParameter_ge hμ₁ hStep
  rw [← hfStep] at hRate₂ hRate₃
  have hRate : cost.step depth * D ^ b ≤ freq ^ (1 / 32 : ℝ) := hRate₁.trans hRate₂
  have hLossBudget : (D ^ r) ^ (6 : ℕ) ≤ cost.step depth * D ^ b := by
    rw [← pow_mul, Nat.mul_comm r 6]
    exact (pow_le_pow_right₀ hD hbLoss).trans (le_mul_of_one_le_left (by positivity) (hGamma depth))
  refine
    { parent_ge_two := hμ
      child_ge_two := hfreq
      child_le_next := hMono (Nat.le_succ _)
      order_le_next := hOrder
      order_le_depth := hDepth
      depth_succ_le_threshold_order := hDepthThreshold
      analytic_le := hAnalytic
      cutoff_tail_le := hCutoff
      cutoff_large := hZero.trans (hMono (Nat.zero_le _))
      gamma_le := hStep
      mean_le := hMean
      radius_exponent := hbRadius
      profile_exponent := hbProfile
      loss_exponent := hbLoss
      absolute_exponent := hbAbsolute
      coframe_dominates := le_self_pow₀ hμ₁ (by decide)
      radius_pos := inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD) a)
      radius_le_one := (inv_le_one₀ (pow_pos (zero_lt_one.trans_le hD) a)).mpr (one_le_pow₀ hD)
      phase_width_pos := Real.rpow_pos_of_pos (zero_lt_two.trans_le hfreq) _
      step_rate := hRate
      step_rate_mul_parent := hRate₃
      flow_small := stepSmall_of_rate (one_le_two.trans hfreq) hRate
      recurrence_small := stepSmall_of_rate (one_le_two.trans hfreq) (hLossBudget.trans hRate)
      mean_rate := ?_
      full_wave_rate := ?_
      full_parent_rate := ?_
      cutoff_tail_rate := ?_
      residual_rate := ?_ }
  · intro m hm
    rw [P.frequency_step i]
    exact frequencySchedule_lowOrder_mean_budget hμ₁
      (hMean m (hm.trans ((le_max_right _ _).trans (hDepth.trans (Nat.le_succ _)))))
      P.exponentParameter_ge hm
  · intro C hC
    rw [P.frequency_step i]
    exact frequencySchedule_fullOrder_wave_budget hμ₁ hC P.exponentParameter_ge
  · intro C hC
    rw [P.frequency_step i]
    exact frequencySchedule_fullOrder_parent_budget hμ₁ hC P.exponentParameter_ge
  · rw [P.frequency_step (i + 1), P.frequency_step i]
    exact frequencySchedule_cutoff_tail_budget P.exponentParameter_ge hμ
  · rw [hNextStep]
    exact frequencySchedule_residual_budget hfreq P.exponentParameter_ge


/-- A parameter record with the threshold `𝓑` itself (Subsection 1.5, (1.13)-(1.14)), for any
`𝓑` with the floor (1.13), any `N` above `N₁`, any strength constant `C ≥ 2` and comparison
constant `C₀ ≥ 240`: the schedule is `frequencySchedule_exists` and the lifetime bounds (7.7)
come from `exists_lifetime_threshold_of_lemma13` (which takes (1.15) from `h1_3`). -/
theorem exists_parameters_of_threshold (h1_3 : Statement.lemma_1_3) (b C₀ : ℕ) (C N₀ : ℝ) (B : ℕ → ℝ)
    (hb : 1 ≤ b) (hC₀ : 240 ≤ C₀) (hC : 2 ≤ C) (hBPos : ∀ s, 1 ≤ s → 0 < B s)
    (hFloor : ∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) :
    ∃ N₁ : ℝ, ∀ N ≥ N₁, ∃ P : InductiveEulerParameters,
      P.exponentParameter = b ∧ P.comparisonConstant = C₀ ∧ P.strengthConstant = C ∧
      P.threshold = B ∧ P.frequency 0 = N ∧ N₀ ≤ P.frequency 0 ∧ P.LifetimeBounds := by
  obtain ⟨NT, hNT⟩ := exists_lifetime_threshold_of_lemma13 h1_3
  refine ⟨max (B 1) (max NT N₀), fun N hN => ?_⟩
  have hB1 : B 1 ≤ N := (le_max_left _ _).trans hN
  have hLog : 0 < Real.log (B 1) := lt_of_lt_of_le
    (by unfold frequencyExponent; positivity) (hFloor 1 le_rfl)
  have hN1 : 1 < N := ((Real.log_pos_iff (hBPos 1 le_rfl).le).1 hLog).trans_le hB1
  obtain ⟨q, f, hq, hf, hstep, horder⟩ := frequencySchedule_exists b B N hb hN1.le hB1
  let P : InductiveEulerParameters :=
    { exponentParameter := b
      threshold := B
      order := q
      frequency := f
      exponentParameter_ge := hb
      initial_order := hq
      initial_threshold := hf.symm ▸ hB1
      frequency_step := hstep
      order_maximum := horder
      threshold_pos := hBPos
      threshold_floor := hFloor
      strengthConstant := C
      strengthConstant_ge := hC
      comparisonConstant := C₀
      comparisonConstant_ge := hC₀ }
  have hN₀ : N₀ ≤ P.frequency 0 :=
    (le_max_right NT N₀).trans ((le_max_right _ _).trans (hN.trans hf.ge))
  exact ⟨P, rfl, rfl, rfl, rfl, hf, hN₀, hNT P ((le_max_left NT N₀).trans
    ((le_max_right _ _).trans (hN.trans hf.ge)))⟩

end

end TorusEuler.Paper.Lib.S678a
