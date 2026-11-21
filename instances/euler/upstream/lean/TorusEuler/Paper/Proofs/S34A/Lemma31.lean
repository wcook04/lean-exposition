import TorusEuler.Paper.S34A.Statements

/-! Conditional proof of **Lemma 3.1** of the latest manuscript (package S34A). -/

namespace TorusEuler.Paper

/-- Proof of **Lemma 3.1** (`cc:uf:exact:lem:profile`,
sections/04_localized_wave.tex:152–160), following the TeX proof at
sections/04_localized_wave.tex:161–175. The TeX proof fixes an even bump `ψ`,
sets `F_h'(s) = (ψ(s/h) - c_h)/(1 - c_h)` with `F_h(0) = 0`, and reads off oddness,
periodicity, the zero-mean primitive `P_h`, the slope bounds `-2c_h ≤ F_h' ≤ 1`
(the profile conditions (1.10)), `‖F_h‖_∞ ≤ 2c_h`, and the higher bounds
`C_j h^{1-j}`. The Lean family `waveProfile h` is exactly this construction
(WaveProfile.lean), and `lemma31_waveProfile` (the row's own content) collects the
listed properties for it. The lemma cites no numbered result, so the proof has no
hypotheses. -/
theorem Proof.lemma_3_1 : Statement.lemma_3_1 := by
  obtain ⟨C, hC, h1, h2⟩ := lemma31_waveProfile
  exact ⟨C, hC, h1, h2⟩

end TorusEuler.Paper
