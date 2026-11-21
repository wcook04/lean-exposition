import TorusEuler.Paper.S678.Statements

/-! # Shared glue for the Section 8 proofs of package S678a (copy of the glue of package S678b)

Elementary consequences of the parameter record `InductiveEulerParameters` and of the
predicate `Theorem71Conclusions` that the proofs of Propositions 8.1, 8.2, 8.4 and
Corollary 8.3 read: the initial frequency is at least `2` (from (1.13) and `N ≥ 𝓑(1)`), the
activation times are nondecreasing and stay below `T_∞`, and the consequences of Lemma 1.3
(`q_j → ∞` and (1.15)) for the schedule of a parameter record, obtained from the statement of
Lemma 1.3 (a hypothesis), never from its library proof. -/

open Filter Set
open scoped Topology

namespace TorusEuler.Paper.Lib.S678a

/-- The initial frequency of every parameter record is at least `2`: (1.13) at `s = 1` gives
`log 𝓑(1) ≥ 4K(2)^3 ≥ 1`, hence `λ_0 = N ≥ 𝓑(1) ≥ e^{4K(2)^3} ≥ 2`
(sections/01b_parameters.tex, (1.13) and `N ≥ 𝓑(1)`). -/
theorem two_le_frequency_zero (P : InductiveEulerParameters) : 2 ≤ P.frequency 0 := by
  have hK : (1 : ℝ) ≤ 4 * (frequencyExponent P.exponentParameter (1 + 1) : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ frequencyExponent P.exponentParameter (1 + 1) := by
      have := P.exponentParameter_ge
      unfold frequencyExponent
      push_cast
      have : (1 : ℝ) ≤ P.exponentParameter := by exact_mod_cast this
      nlinarith
    nlinarith [one_le_pow₀ (n := 3) h1]
  have hlog := P.threshold_floor 1 le_rfl
  have hexp : Real.exp (4 * (frequencyExponent P.exponentParameter (1 + 1) : ℝ) ^ 3) ≤
      P.threshold 1 :=
    (Real.le_log_iff_exp_le (P.threshold_pos 1 le_rfl)).1 hlog
  have h2 := Real.add_one_le_exp (4 * (frequencyExponent P.exponentParameter (1 + 1) : ℝ) ^ 3)
  linarith [P.initial_threshold]

/-- The activation times of a construction satisfying the conclusions of Theorem 7.1 are
nondecreasing: `0 = t_1 = t_2 < t_3 < ⋯` (`first_times`, `times_increase`; the unused value
at index `0` is `0`). -/
theorem activation_mono {P : InductiveEulerParameters} {c : InductiveEulerConstruction P}
    {C T : ℝ} (h71 : Theorem71Conclusions c C T) : Monotone c.stages.activation := by
  apply monotone_nat_of_le_succ
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [c.stages.activation_zero, h71.first_times.1]
    · simp [h71.first_times.1, h71.first_times.2]
  · exact (h71.times_increase n hn).le

/-- Every activation time lies strictly before `T_∞`: the times increase strictly from `t_2`
on and converge to `T_∞` (`lifetime`). -/
theorem activation_lt {P : InductiveEulerParameters} {c : InductiveEulerConstruction P}
    {C T : ℝ} (h71 : Theorem71Conclusions c C T) (j : ℕ) : c.stages.activation j < T := by
  have hmono := activation_mono h71
  have hle (n : ℕ) : c.stages.activation n ≤ T := hmono.ge_of_tendsto h71.lifetime.2.1 n
  rcases Nat.lt_or_ge j 2 with hj | hj
  · calc c.stages.activation j ≤ c.stages.activation 2 := hmono (by omega)
      _ < c.stages.activation 3 := h71.times_increase 2 le_rfl
      _ ≤ T := hle 3
  · exact (h71.times_increase j hj).trans_le (hle (j + 1))

/-- **Lemma 1.3 applied to a parameter record.** The schedule `(q_j, λ_j)` of every
`InductiveEulerParameters` satisfies the hypotheses of `Statement.lemma_1_3` (the record
stores (1.13), `N ≥ 𝓑(1)` and (1.14) with the index shift `j = i + 1`). Hence `q_j → ∞` and
(1.15) `L_{j+1} = 4 log λ_{j+2} ≤ (log λ_{j-1})^2`, written here at `j = i + 1`. Both
conclusions come from the hypothesis `h13`. -/
theorem lemma13_schedule (h13 : Statement.lemma_1_3) (P : InductiveEulerParameters) :
    Tendsto P.order atTop atTop ∧
      ∀ i, 4 * Real.log (P.frequency (i + 3)) ≤ Real.log (P.frequency i) ^ 2 := by
  obtain ⟨-, ht, hl⟩ := h13 P.exponentParameter P.threshold (P.frequency 0) P.order P.frequency
    P.exponentParameter_ge (fun s hs => ⟨P.threshold_pos s hs, P.threshold_floor s hs⟩)
    P.initial_threshold P.initial_order rfl
    (fun j hj => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact P.frequency_step i)
    (fun j hj => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact P.order_maximum i)
  exact ⟨ht, fun i => by simpa [Schedule.L] using hl (i + 1) (Nat.succ_pos i)⟩

end TorusEuler.Paper.Lib.S678a
