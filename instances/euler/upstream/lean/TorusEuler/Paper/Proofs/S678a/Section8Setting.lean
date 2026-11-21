import TorusEuler.Paper.S678.Statements

/-! # The opening of Section 8 from Theorem 7.1

Proof of `Statement.Text.section8_setting` (sections/09_limit.tex:2) from
`Statement.theorem_7_1`. -/

namespace TorusEuler.Paper

namespace Lib.S678a

/-- An admissible threshold `𝓑` of Subsection 1.5 exists above every majorant `F`: the partial
sums `𝓑(s) = ∑_{t ≤ s} (|F(t)| + exp(4K(t+1)^3))` are positive, nondecreasing, bound `F` and satisfy
the floor (1.13). Glue (the text lets `𝓑` be "any function with these properties"). -/
theorem exists_admissibleThreshold (b : ℕ) (F : ℕ → ℝ) : ∃ B : ℕ → ℝ, AdmissibleThreshold b F B := by
  let g : ℕ → ℝ := fun t => |F t| + Real.exp (4 * (frequencyExponent b (t + 1) : ℝ) ^ 3)
  have hg : ∀ t, 0 < g t := fun t => add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.exp_pos _)
  have hsum : ∀ s, g s ≤ ∑ t ∈ Finset.range (s + 1), g t := fun s =>
    Finset.single_le_sum (f := g) (fun t _ => (hg t).le) (Finset.self_mem_range_succ s)
  refine ⟨fun s => ∑ t ∈ Finset.range (s + 1), g t, ?_, ?_, ?_, ?_⟩
  · intro s t _ hst
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => (hg i).le)
  · intro s _
    exact (le_abs_self (F s)).trans ((le_add_of_nonneg_right (Real.exp_pos _).le).trans (hsum s))
  · intro s _
    exact (hg s).trans_le (hsum s)
  · intro s _
    have h1 : Real.exp (4 * (frequencyExponent b (s + 1) : ℝ) ^ 3) ≤ ∑ t ∈ Finset.range (s + 1), g t :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hsum s)
    exact (Real.le_log_iff_exp_le ((hg s).trans_le (hsum s))).mpr h1

end Lib.S678a

/-- Proof of the unnumbered opening of **Section 8** (sections/09_limit.tex:2, "On the common
interval `[0,T_∞]` of Theorem 7.1") from `h7_1 : Statement.theorem_7_1`. The cutoff symbol of
Appendix B (`exists_appendixB_cutoffSymbol`) and the floor `a₀ = 0` are fed to Theorem 7.1; the
admissible function `𝓑` (`Lib.S678a.exists_admissibleThreshold`) and a large frequency `N = N₁`
then give the construction with `Theorem71Conclusions c C T` (the step data is dropped). -/
theorem Proof.Text.section8_setting_of (h7_1 : Statement.theorem_7_1) :
    Statement.Text.section8_setting := by
  obtain ⟨ψ, hψ⟩ := exists_appendixB_cutoffSymbol
  obtain ⟨b, a, F, _, _, h⟩ := h7_1 ψ hψ 0
  obtain ⟨B, hB⟩ := Lib.S678a.exists_admissibleThreshold b F
  obtain ⟨N₁, hN⟩ := h B hB
  obtain ⟨P, c, T, _, _, _, _, hconc, _⟩ := hN N₁ le_rfl
  exact ⟨P, c, _, T, hconc⟩

end TorusEuler.Paper
