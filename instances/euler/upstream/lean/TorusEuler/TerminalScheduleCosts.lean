import TorusEuler.InductiveStepNumericalBudgets

/-! The schedule used for the stronger terminal regularity conclusion. -/

open Filter

namespace TorusEuler.InductiveEulerParameters

noncomputable section

/-- Add the auxiliary fixed-order costs to the threshold table. The three
arguments of each new cost are time order, spatial order, and depth. A
requested spatial order `m` can include a reserve depending on time order
and depth. -/
def StepCosts.withTerminal {ι κ : Type*} (cost : StepCosts ι)
    (terminal : κ → ℕ → ℕ → ℕ → ℝ) (reserve : ℕ → ℕ → ℕ) : StepCosts (ι ⊕ κ) where
  analytic
    | .inl j, m, d => cost.analytic j m d
    | .inr j, m, d => ∑ q ∈ Finset.range (m + 1),
        ∑ n ∈ Finset.range (m + reserve q d + 1), |terminal j q n d|
  cutoffTail := cost.cutoffTail
  step := cost.step
  mean := cost.mean

/-- The original physical estimates retain their numerical budget when
the frequency schedule uses the enlarged table. -/
theorem StepNumericalBudget.of_withTerminal {ι κ : Type*} {P : InductiveEulerParameters}
    {i a p r power : ℕ} {cutoff : ℝ} {cost : StepCosts ι} {terminal : κ → ℕ → ℕ → ℕ → ℝ}
    {reserve : ℕ → ℕ → ℕ}
    (h : P.StepNumericalBudget i a p r power cutoff (cost.withTerminal terminal reserve)) :
    P.StepNumericalBudget i a p r power cutoff cost := by
  exact { h with analytic_le := fun j m hm => h.analytic_le (.inl j) m hm }

/-- The enlarged threshold bounds each auxiliary cost separately. -/
theorem abs_terminalCost_le_withTerminalThreshold {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ℕ) (cost : StepCosts ι) (terminal : κ → ℕ → ℕ → ℕ → ℝ)
    (reserve : ℕ → ℕ → ℕ) (j : κ) {s q m d : ℕ}
    (hq : q ≤ 7 * frequencyExponent b s)
    (hm : m ≤ 7 * frequencyExponent b s + reserve q d)
    (hd : d ≤ 7 * frequencyExponent b s) :
    |terminal j q m d| ≤ fixedOrderThreshold b (cost.withTerminal terminal reserve).table s := by
  let S := 7 * frequencyExponent b s
  let timeCost (n k : ℕ) := ∑ v ∈ Finset.range (n + reserve k d + 1), |terminal j k v d|
  let orderCost (n : ℕ) := ∑ k ∈ Finset.range (n + 1), timeCost n k
  have hTime (n k : ℕ) : 0 ≤ timeCost n k := Finset.sum_nonneg fun v _ => abs_nonneg _
  have hOrder (n : ℕ) : 0 ≤ orderCost n := Finset.sum_nonneg fun k _ => hTime n k
  have hTable := abs_fixedOrderCost_le_threshold b (cost.withTerminal terminal reserve).table
    (.analytic (.inr j)) (m := S) (p := d) le_rfl hd
  change |(∑ n ∈ Finset.range (S + 3 * d + 1), |orderCost n|)| ≤ _ at hTable
  rw [abs_of_nonneg (Finset.sum_nonneg fun n _ => abs_nonneg (orderCost n))] at hTable
  calc
    |terminal j q m d| ≤ timeCost S q :=
      Finset.single_le_sum (fun v _ => abs_nonneg (terminal j q v d))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    _ ≤ orderCost S := Finset.single_le_sum (fun k _ => hTime S k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
    _ = |orderCost S| := (abs_of_nonneg (hOrder S)).symm
    _ ≤ ∑ n ∈ Finset.range (S + 3 * d + 1), |orderCost n| :=
      Finset.single_le_sum (fun n _ => abs_nonneg (orderCost n)) (Finset.mem_range.mpr (by omega))
    _ ≤ _ := hTable

/-- Choose the threshold before the initial frequency, with the physical
and auxiliary constants controlled at every step of the same schedule. -/
theorem exists_of_inductiveStepCosts_withTerminal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (cost : StepCosts ι) (terminal : κ → ℕ → ℕ → ℕ → ℝ) (reserve : ℕ → ℕ → ℕ)
    (a p r power b comparison : ℕ) (strength cutoffConstant initialFloor : ℝ)
    (hb : stepExponentFloor a p r power ≤ b) (hComparison : 240 ≤ comparison)
    (hStrength : 2 ≤ strength) (hGamma : ∀ depth, 1 ≤ cost.step depth) :
    ∃ N₁ : ℝ, ∀ N ≥ N₁, ∃ P : InductiveEulerParameters,
      P.exponentParameter = b ∧ P.comparisonConstant = comparison ∧ P.strengthConstant = strength ∧
      P.threshold = fixedOrderThreshold b (cost.withTerminal terminal reserve).table ∧
      P.frequency 0 = N ∧ initialFloor ≤ P.frequency 0 ∧ Real.exp 4 ≤ P.frequency 0 ∧
      P.LifetimeBounds ∧ (∀ i, P.StepNumericalBudget i a p r power cutoffConstant cost) ∧
      ∀ i j q m d, let S := 7 * frequencyExponent b (P.order (i + 2))
        q ≤ S → m ≤ S + reserve q d → d ≤ S → |terminal j q m d| ≤ P.frequency i := by
  obtain ⟨N₁, hChoose⟩ := exists_of_inductiveStepCosts (cost.withTerminal terminal reserve)
    a p r power b comparison strength cutoffConstant initialFloor hb hComparison hStrength hGamma
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨P, hB, hComparisonP, hStrengthP, hThreshold, hN', hFloor, hExp, hLife, hStep⟩ := hChoose N hN
  refine ⟨P, hB, hComparisonP, hStrengthP, hThreshold, hN', hFloor, hExp, hLife,
    fun i => (hStep i).of_withTerminal, ?_⟩
  intro i j q m d S hq hm hd
  have hThresholdLe : fixedOrderThreshold b (cost.withTerminal terminal reserve).table (P.order (i + 2))
      ≤ P.frequency i := by
    rw [← hThreshold]
    exact (P.order_maximum i).1.2.2
  exact (abs_terminalCost_le_withTerminalThreshold b cost terminal reserve j hq hm hd).trans hThresholdLe

theorem terminal_frequency_zero_gt_one (P : InductiveEulerParameters) : 1 < P.frequency 0 := by
  have hb : 0 < P.exponentParameter := P.exponentParameter_ge
  have hLog : 0 < Real.log (P.threshold 1) :=
    (show 0 < 4 * (frequencyExponent P.exponentParameter 2 : ℝ) ^ 3 by
      unfold frequencyExponent; positivity).trans_le (P.threshold_floor 1 le_rfl)
  exact ((Real.log_pos_iff (P.threshold_pos 1 le_rfl).le).1 hLog).trans_le P.initial_threshold

theorem terminal_frequency_mono (P : InductiveEulerParameters) : Monotone P.frequency :=
  frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency P.exponentParameter_ge
    P.terminal_frequency_zero_gt_one.le P.frequency_step

theorem terminal_frequency_tendsto_atTop (P : InductiveEulerParameters) :
    Tendsto P.frequency atTop atTop :=
  frequencySchedule_frequency_tendsto_atTop P.exponentParameter P.order P.frequency
    P.exponentParameter_ge P.terminal_frequency_zero_gt_one P.frequency_step

theorem terminal_order_tendsto_atTop (P : InductiveEulerParameters) : Tendsto P.order atTop atTop :=
  frequencySchedule_order_tendsto_atTop P.threshold P.frequency P.order P.initial_order P.initial_threshold
    P.terminal_frequency_mono P.terminal_frequency_tendsto_atTop P.order_maximum

/-- The exponent separating two adjacent frequencies tends to infinity. -/
theorem terminal_frequencyExponent_tendsto_atTop (P : InductiveEulerParameters) :
    Tendsto (fun i : ℕ => frequencyExponent P.exponentParameter (P.order (i + 1))) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) ((tendsto_add_atTop_iff_nat 1).2 P.terminal_order_tendsto_atTop)
  have h := Nat.le_mul_of_pos_left (P.order (i + 1) + 1)
    (Nat.mul_pos (by decide : 0 < (320 : ℕ)) P.exponentParameter_ge)
  exact (Nat.le_succ _).trans h

/-- Every fixed temporal or spatial order fits the enlarged threshold
eventually, including time conversion at the full hierarchy depth. -/
theorem eventually_terminalDerivativeReserve (P : InductiveEulerParameters) (m q : ℕ) :
    ∀ᶠ i : ℕ in atTop, let K := frequencyExponent P.exponentParameter (P.order (i + 2))
      m ≤ 7 * K ∧ q ≤ 7 * K ∧ P.stepDepth i + q + 2 ≤ 7 * K := by
  have hK : Tendsto (fun i : ℕ => frequencyExponent P.exponentParameter (P.order (i + 2))) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).2 P.terminal_frequencyExponent_tendsto_atTop
  filter_upwards [hK.eventually_ge_atTop (max m (q + 2))] with i hi
  intro K
  dsimp only [stepDepth]
  have hm := (le_max_left m (q + 2)).trans hi
  have hq := (le_max_right m (q + 2)).trans hi
  dsimp only [K]
  omega

/-- A fixed polynomial in the parent frequency is eventually bounded by
any prescribed positive power of the new frequency. -/
theorem eventually_parentPolynomial_le_child_rpow (P : InductiveEulerParameters)
    (C A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, C * P.frequency i ^ A ≤ P.frequency (i + 1) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_ge ((1 + A) / ε)
  filter_upwards [P.terminal_frequency_tendsto_atTop.eventually_ge_atTop C,
    P.terminal_frequencyExponent_tendsto_atTop.eventually_ge_atTop k] with i hC hK
  let μ := P.frequency i
  let K := frequencyExponent P.exponentParameter (P.order (i + 1))
  have hμ : 1 ≤ μ := P.terminal_frequency_zero_gt_one.le.trans (P.terminal_frequency_mono (Nat.zero_le i))
  have hK' : (1 + A) / ε ≤ (K : ℝ) := hk.trans (by exact_mod_cast hK)
  have hExp : 1 + A ≤ (K : ℝ) * ε := (div_le_iff₀ hε).1 hK'
  calc
    C * μ ^ A ≤ μ * μ ^ A := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (zero_le_one.trans hμ) _)
    _ = μ ^ (1 + A) := by nth_rw 1 [← Real.rpow_one μ]; rw [← Real.rpow_add (zero_lt_one.trans_le hμ)]
    _ ≤ μ ^ ((K : ℝ) * ε) := Real.rpow_le_rpow_of_exponent_le hμ hExp
    _ = P.frequency (i + 1) ^ ε := by
      rw [P.frequency_step i, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hμ)]

/-- The adjacent-frequency separation absorbs a fixed parent polynomial
in the smallness conditions on the mixed recurrence. -/
theorem eventually_parentPolynomial_mul_child_rpow_le_one (P : InductiveEulerParameters)
    (C A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, C * P.frequency i ^ A * P.frequency (i + 1) ^ (-ε) ≤ 1 := by
  filter_upwards [P.eventually_parentPolynomial_le_child_rpow C A ε hε] with i hCost
  have hF : 0 < P.frequency (i + 1) :=
    (zero_lt_one.trans P.terminal_frequency_zero_gt_one).trans_le (P.terminal_frequency_mono (Nat.zero_le _))
  calc
    _ ≤ P.frequency (i + 1) ^ ε * P.frequency (i + 1) ^ (-ε) :=
      mul_le_mul_of_nonneg_right hCost (Real.rpow_nonneg hF.le _)
    _ = 1 := by rw [← Real.rpow_add hF, add_neg_cancel, Real.rpow_zero]

/-- Extracting a time derivative from the scaled norms incurs at most
a fixed power of the parent frequency at each time order. -/
theorem terminal_slab_inv_le (P : InductiveEulerParameters)
    (hInitial : Real.exp 1 ≤ P.frequency 0) (i : ℕ) {activation : ℝ} (hActivation : 0 ≤ activation) :
    (P.slab (i + 1) activation)⁻¹ ≤ P.frequency i ^ (1 / 8 : ℝ) := by
  have hF : 0 < P.frequency i :=
    (zero_lt_one.trans P.terminal_frequency_zero_gt_one).trans_le (P.terminal_frequency_mono (Nat.zero_le _))
  have hLog : 1 ≤ Real.log (P.frequency (i + 3)) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (hInitial.trans (P.terminal_frequency_mono (Nat.zero_le (i + 3))))
    rwa [Real.log_exp] at h
  have hGain : 1 ≤ (4 * Real.log (P.frequency (i + 3))) ^ 3 := one_le_pow₀ (by linarith)
  have hHalf : P.frequency i ^ (-1 / 8 : ℝ) ≤ inductionHalfLength P.frequency i :=
    le_mul_of_one_le_right (Real.rpow_nonneg hF.le _) hGain
  have hSlab : P.frequency i ^ (-1 / 8 : ℝ) ≤ P.slab (i + 1) activation := by
    rw [P.slab_succ]
    linarith only [hActivation, hHalf, Real.rpow_nonneg hF.le (-1 / 8 : ℝ)]
  calc
    _ ≤ (P.frequency i ^ (-1 / 8 : ℝ))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hF _) hSlab
    _ = _ := by rw [← Real.rpow_neg hF.le]; norm_num

end

end TorusEuler.InductiveEulerParameters
