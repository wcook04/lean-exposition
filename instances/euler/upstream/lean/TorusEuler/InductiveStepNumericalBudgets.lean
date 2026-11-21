import TorusEuler.InductiveParameterSelection

/-! Numerical bounds for the Eulerian stage construction on the prescribed
frequency schedule. -/

open Set

namespace TorusEuler.InductiveEulerParameters

noncomputable section

/-- The expansion depth in Theorem 7.1 for the step from stage `i`. -/
def stepDepth (P : InductiveEulerParameters) (i : ℕ) : ℕ :=
  6 * frequencyExponent P.exponentParameter (P.order (i + 2))

/-- Fixed-order constants supplied by the analytic estimates. -/
structure StepCosts (ι : Type*) where
  analytic : ι → ℕ → ℕ → ℝ
  cutoffTail : ℕ → ℝ
  step : ℕ → ℝ
  mean : ℕ → ℕ → ℝ

inductive StepCostIndex (ι : Type*)
  | analytic (j : ι)
  | cutoffTail
  | step
  | mean
  deriving Fintype

/-- A requested order of `m` reserves the analytic constants through
`m + 3 * p` at expansion depth `p`. -/
def StepCosts.table {ι : Type*} (cost : StepCosts ι) : StepCostIndex ι → ℕ → ℕ → ℝ
  | .analytic j, m, p => ∑ r ∈ Finset.range (m + 3 * p + 1), |cost.analytic j r p|
  | .cutoffTail, _, p => cost.cutoffTail p
  | .step, _, p => cost.step p
  | .mean, m, p => cost.mean m p

/-- The integer parameter can be fixed once the radius, profile loss,
recurrence loss and other absolute powers are chosen. -/
def stepExponentFloor (a p r absolutePower : ℕ) : ℕ :=
  max 1 (max absolutePower (max (max a 1 + (max a 1 + p) + 1) (6 * r)))

/-- A common prefactor bounds a sum of estimates with fixed parent powers. -/
theorem sum_mul_parentPower_le {ι : Type*} (s : Finset ι) {D Γ : ℝ} {b : ℕ}
    (c : ι → ℝ) (exponent : ι → ℕ) (hD : 1 ≤ D)
    (hc : ∀ j ∈ s, 0 ≤ c j) (hb : ∀ j ∈ s, exponent j ≤ b) (hΓ : ∑ j ∈ s, c j ≤ Γ) :
    ∑ j ∈ s, c j * D ^ exponent j ≤ Γ * D ^ b := by
  calc
    _ ≤ ∑ j ∈ s, c j * D ^ b := Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (hb j hj)) (hc j hj)
    _ = (∑ j ∈ s, c j) * D ^ b := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hΓ (pow_nonneg (zero_le_one.trans hD) b)

/-- Scale and constant inequalities for one scheduled physical step.
The analytic row bound includes the derivative reserve of the level induction. -/
structure StepNumericalBudget {ι : Type*} (P : InductiveEulerParameters) (i : ℕ)
    (a p r absolutePower : ℕ) (cutoffConstant : ℝ) (cost : StepCosts ι) : Prop where
  parent_ge_two : 2 ≤ P.frequency i
  child_ge_two : 2 ≤ P.frequency (i + 1)
  child_le_next : P.frequency (i + 1) ≤ P.frequency (i + 2)
  order_le_next : P.order (i + 1) ≤ P.order (i + 2)
  order_le_depth : max 2 (P.order (i + 1)) ≤ P.stepDepth i
  depth_succ_le_threshold_order :
    P.stepDepth i + 1 ≤ 7 * frequencyExponent P.exponentParameter (P.order (i + 2))
  analytic_le : ∀ j m, m ≤ (P.stepDepth i + 1) + 3 * P.stepDepth i →
    |cost.analytic j m (P.stepDepth i)| ≤ P.frequency i
  cutoff_tail_le : cost.cutoffTail (P.stepDepth i) ≤ P.frequency i
  cutoff_large : max 2 ((2 * cutoffConstant) ^ (2 : ℕ)) ≤ P.frequency (i + 2)
  gamma_le : cost.step (P.stepDepth i) ≤ P.frequency i
  mean_le : ∀ m ≤ P.stepDepth i + 1, cost.mean m (P.stepDepth i) ≤ P.frequency i
  radius_exponent : a + 1 ≤ P.exponentParameter
  profile_exponent : max a 1 + (max a 1 + p) + 1 ≤ P.exponentParameter
  loss_exponent : 6 * r ≤ P.exponentParameter
  absolute_exponent : absolutePower ≤ P.exponentParameter
  coframe_dominates : P.frequency i ≤ P.frequency i ^ (9 : ℕ)
  radius_pos : 0 < (((P.frequency i ^ (9 : ℕ)) ^ a)⁻¹)
  radius_le_one : (((P.frequency i ^ (9 : ℕ)) ^ a)⁻¹) ≤ 1
  phase_width_pos : 0 < P.frequency (i + 1) ^ (-1 / 2 : ℝ)
  step_rate : cost.step (P.stepDepth i) * (P.frequency i ^ (9 : ℕ)) ^ P.exponentParameter ≤
    P.frequency (i + 1) ^ (1 / 32 : ℝ)
  step_rate_mul_parent :
    (cost.step (P.stepDepth i) * (P.frequency i ^ (9 : ℕ)) ^ P.exponentParameter) * P.frequency i ≤
      P.frequency (i + 1) ^ (1 / 16 : ℝ)
  flow_small : (cost.step (P.stepDepth i) * (P.frequency i ^ (9 : ℕ)) ^ P.exponentParameter) *
    P.frequency (i + 1) ^ (-1 / 12 : ℝ) ≤ 1
  recurrence_small : (((P.frequency i ^ (9 : ℕ)) ^ r) ^ (6 : ℕ)) *
    P.frequency (i + 1) ^ (-1 / 12 : ℝ) ≤ 1
  mean_rate : ∀ m ≤ P.order (i + 1),
    cost.mean m (P.stepDepth i) * (P.frequency i ^ (9 : ℕ)) ^ (P.exponentParameter * (m + 2)) ≤
      P.frequency (i + 1) ^ (1 / 16 : ℝ)
  full_wave_rate : ∀ C ≤ P.frequency i,
    C * (P.frequency i ^ (9 : ℕ)) ^ (P.exponentParameter * (P.stepDepth i + 2)) ≤
      P.frequency (i + 1) ^ (((P.stepDepth i : ℝ) + 2) / 32)
  full_parent_rate : ∀ C ≤ P.frequency i,
    C * P.frequency i ^ (5 * (P.stepDepth i + 1) + 1) ≤
      P.frequency (i + 1) ^ (P.stepDepth i + 2)
  cutoff_tail_rate : 9 * P.frequency i * P.frequency (i + 1) ^
      (5 * (2 - (P.stepDepth i : ℝ)) + 4 * ((P.stepDepth i : ℝ) + 1)) ≤
    P.frequency (i + 2) ^ (-5 : ℝ)
  residual_rate : 2 * P.frequency (i + 1) ^ (2 + 1 / 16 : ℝ) *
      P.frequency (i + 2) ^ (-4 : ℝ) ≤ P.frequency (i + 2) ^ (-7 / 2 : ℝ)

private theorem stepSmall_of_rate {freq C : ℝ} (hf : 1 ≤ freq)
    (hC : C ≤ freq ^ (1 / 32 : ℝ)) : C * freq ^ (-1 / 12 : ℝ) ≤ 1 := by
  calc
    _ ≤ freq ^ (1 / 32 : ℝ) * freq ^ (-1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = freq ^ (-5 / 96 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hf)]
      norm_num
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hf (by norm_num)

set_option maxHeartbeats 1200000 in
/-- The stored order maximum gives the constants and powers for the same
scheduled step. -/
theorem stepNumericalBudget_of_threshold {ι : Type*} [Fintype ι]
    (P : InductiveEulerParameters) (cost : StepCosts ι) (cutoffConstant : ℝ)
    (hThreshold : P.threshold = fixedOrderThreshold P.exponentParameter cost.table)
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
    rw [← hThreshold]
    exact (P.order_maximum i).1.2.2
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

set_option maxHeartbeats 550000 in
/-- Choose an initial frequency for the given analytic constants and fixed
powers, with the frequency steps and order maxima of (1.14). -/
theorem exists_of_inductiveStepCosts {ι : Type*} [Fintype ι]
    (cost : StepCosts ι) (a p r absolutePower b comparison : ℕ)
    (strength cutoffConstant initialFloor : ℝ)
    (hb : stepExponentFloor a p r absolutePower ≤ b)
    (hComparison : 240 ≤ comparison) (hStrength : 2 ≤ strength)
    (hGamma : ∀ depth, 1 ≤ cost.step depth) :
    ∃ N₁ : ℝ, ∀ N ≥ N₁, ∃ P : InductiveEulerParameters,
      P.exponentParameter = b ∧ P.comparisonConstant = comparison ∧ P.strengthConstant = strength ∧
      P.threshold = fixedOrderThreshold b cost.table ∧ P.frequency 0 = N ∧
      initialFloor ≤ P.frequency 0 ∧ Real.exp 4 ≤ P.frequency 0 ∧ P.LifetimeBounds ∧
      ∀ i, P.StepNumericalBudget i a p r absolutePower cutoffConstant cost := by
  let floor := max initialFloor (max (Real.exp 4) (max 2 ((2 * cutoffConstant) ^ (2 : ℕ))))
  have hbOne : 1 ≤ b := (le_max_left _ _).trans hb
  obtain ⟨N₁, hChoose⟩ := exists_of_fixedOrderCosts b comparison strength floor cost.table
    hbOne hComparison hStrength
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨P, hB, hComparisonP, hStrengthP, hThreshold, hInitial, hFloor, hLife, _⟩ := hChoose N hN
  refine ⟨P, hB, hComparisonP, hStrengthP, hThreshold, hInitial, (le_max_left _ _).trans hFloor,
    (le_max_left _ _).trans ((le_max_right _ _).trans hFloor), hLife, fun i => ?_⟩
  exact stepNumericalBudget_of_threshold P cost cutoffConstant (hThreshold.trans (by rw [hB]))
    (hb.trans hB.ge) ((le_max_right _ _).trans ((le_max_right _ _).trans hFloor)) hGamma i

end

end TorusEuler.InductiveEulerParameters
