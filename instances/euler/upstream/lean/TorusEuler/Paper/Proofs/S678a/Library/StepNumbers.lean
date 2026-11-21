import TorusEuler.Paper.Proofs.S678a.Library.StepCutoff
import TorusEuler.InductiveStepNumericalBudgets

/-! # The numerical hypotheses of one step from the cost table (package S678a)

`StepNumbers` collects the numerical inequalities that the conversion of Section 5 into one
stage of the construction uses (sections/08b_induction.tex:238-248 and :376-461: the choice of
`b` and of the thresholds `𝓑` makes every fixed-order constant at most `λ_j`). They are the
fields of `P.StepNumericalBudget` for a cost table whose entries majorize the constants of
Lemmas 5.8-5.10, Proposition 5.11 and Lemma B.1 and the Bernstein jets (`stepNumbers_of_budget`). -/

open Set

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler TorusEuler.InductiveEulerParameters

noncomputable section

/-- The numerical hypotheses for the step with parent stage `i`. -/
structure StepNumbers (P : InductiveEulerParameters) (i : ℕ) (Γ : ℕ → ℝ) (K58 : ℕ → ℕ → ℝ)
    (Cc : ℝ) (K11 Ct : ℕ → ℝ) (Cparent Cstep Cmean : ℝ) : Prop where
  flow_small : Γ (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) *
    ((P.frequency i ^ 9) ^ P.exponentParameter) * P.frequency (i + 1) ^ (-1 / 12 : ℝ) ≤ 1
  residual : ∀ dS : ℝ, dS ≤ P.frequency i * P.frequency (i + 2) ^ (-4 : ℝ) →
    Γ (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) *
      ((P.frequency i ^ 9) ^ P.exponentParameter) * P.frequency (i + 1) ^ (2 : ℝ) *
      (P.frequency (i + 1) ^ (-2 * (6 * (frequencyExponent P.exponentParameter (P.order (i + 2)) : ℝ)) / 3) + dS) ≤
    P.frequency (i + 2) ^ (-7 / 2 : ℝ)
  ct_nonneg : 0 ≤ Ct (6 * frequencyExponent P.exponentParameter (P.order (i + 2)))
  ct_le : Ct (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) ≤ P.frequency i
  cc_nonneg : 0 ≤ Cc
  k11_le : K11 (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) ≤ P.frequency i
  large : max 2 ((2 * Cc) ^ (2 : ℕ)) ≤ P.frequency (i + 2)
  jets_le : (3 * (6 * (frequencyExponent P.exponentParameter (P.order (i + 2)) : ℝ) + 1)) *
    Cparent ≤ P.frequency i
  parent_nonneg : 0 ≤ Cparent
  osc_le : K58 (6 * frequencyExponent P.exponentParameter (P.order (i + 2)))
    (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) ≤ P.frequency i
  step0 : K58 0 (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) *
    ((P.frequency i ^ 9) ^ P.exponentParameter) ≤ Cstep
  stepΓ : Γ (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) *
    ((P.frequency i ^ 9) ^ P.exponentParameter) ≤ Cstep
  step32 : Cstep ≤ P.frequency (i + 1) ^ (1 / 32 : ℝ)
  mean_le : ∀ m ≤ P.order (i + 1),
    K58 m (6 * frequencyExponent P.exponentParameter (P.order (i + 2))) ≤ Cmean
  mean_mu : Cmean ≤ P.frequency i

/-- **The numerical hypotheses from the budget of the schedule** (sections/08b_induction.tex:238-248):
for a cost table whose entries majorize the constants, the fields of `P.StepNumericalBudget i`
give `StepNumbers`, with `C_parent = Cj`, `C_step = Γ D^b`, `C_mean = λ_i`. -/
theorem stepNumbers_of_budget {P : InductiveEulerParameters} {i : ℕ} {a p r pw : ℕ}
    {cost : StepCosts Unit} {Γ : ℕ → ℝ} {K58 : ℕ → ℕ → ℝ} {Cc : ℝ} {K11 Ct Cj : ℕ → ℝ}
    (num : P.StepNumericalBudget i a p r pw Cc cost)
    (hΓc : ∀ q, Γ q = cost.step q) (hΓ1 : ∀ q, 1 ≤ cost.step q)
    (hK58 : ∀ m q, K58 m q ≤ cost.mean m q) (hK580 : ∀ q, K58 0 q ≤ Γ q)
    (hCt : ∀ q, Ct q ≤ cost.cutoffTail q) (hK11 : ∀ q, K11 q ≤ cost.cutoffTail q)
    (hCt0 : ∀ q, 0 ≤ Ct q) (hana : ∀ q : ℕ, 3 * ((q : ℝ) + 1) * Cj q ≤ cost.analytic () 0 q)
    (hCj : ∀ q, 0 ≤ Cj q) (hCc : 0 ≤ Cc) :
    StepNumbers P i Γ K58 Cc K11 Ct (Cj (P.stepDepth i))
      (Γ (P.stepDepth i) * ((P.frequency i ^ 9) ^ P.exponentParameter)) (P.frequency i) where
  flow_small := by
    have := num.flow_small
    rw [← hΓc] at this
    exact this
  residual := by
    intro dS hdS
    have hl : 1 ≤ P.frequency (i + 1) := one_le_two.trans num.child_ge_two
    have hμ : 1 ≤ P.frequency i := one_le_two.trans num.parent_ge_two
    have hX : 0 ≤ Γ (P.stepDepth i) * ((P.frequency i ^ 9) ^ P.exponentParameter) := by
      rw [hΓc]
      exact mul_nonneg (zero_le_one.trans (hΓ1 _))
        (pow_nonneg (pow_nonneg (zero_le_two.trans num.parent_ge_two) _) _)
    have hrate := num.step_rate_mul_parent
    rw [← hΓc] at hrate
    exact residual_size_of_budget (K := frequencyExponent P.exponentParameter (P.order (i + 2)))
      hμ hX hl hdS (P.frequency_step (i + 1)) hrate num.residual_rate
  ct_nonneg := hCt0 _
  ct_le := (hCt _).trans num.cutoff_tail_le
  cc_nonneg := hCc
  k11_le := (hK11 _).trans num.cutoff_tail_le
  large := num.cutoff_large
  jets_le := by
    have h := num.analytic_le () 0 (Nat.zero_le _)
    have h2 := (hana (P.stepDepth i)).trans ((le_abs_self _).trans h)
    simpa [stepDepth] using h2
  parent_nonneg := hCj _
  osc_le := by
    have h := num.mean_le (P.stepDepth i) (Nat.le_succ _)
    exact (hK58 _ _).trans h
  step0 := mul_le_mul_of_nonneg_right (hK580 _)
    (pow_nonneg (pow_nonneg (zero_le_two.trans num.parent_ge_two) _) _)
  stepΓ := le_rfl
  step32 := by
    have := num.step_rate
    rw [← hΓc] at this
    exact this
  mean_le := by
    intro m hm
    have hm' : m ≤ P.stepDepth i + 1 :=
      hm.trans ((le_max_right 2 _).trans (num.order_le_depth.trans (Nat.le_succ _)))
    exact (hK58 _ _).trans (num.mean_le m hm')
  mean_mu := le_rfl

end

end TorusEuler.Paper.Lib.S678a
